// Copyright (c) 2011, David J. Pearce (djp@ecs.vuw.ac.nz)
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//    * Redistributions of source code must retain the above copyright
//      notice, this list of conditions and the following disclaimer.
//    * Redistributions in binary form must reproduce the above copyright
//      notice, this list of conditions and the following disclaimer in the
//      documentation and/or other materials provided with the distribution.
//    * Neither the name of the <organization> nor the
//      names of its contributors may be used to endorse or promote products
//      derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL DAVID J. PEARCE BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

package wy2boogie.translate;

import static wy2boogie.translate.BoogieType.*;

import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.*;
import java.util.stream.Stream;

import static wyil.lang.WyilFile.*;

import wybs.util.AbstractCompilationUnit;
import wyil.lang.WyilFile;
import wyil.type.subtyping.EmptinessTest;
import wyil.type.subtyping.StrictTypeEmptinessTest;
import wyil.type.util.ConcreteTypeExtractor;
import wyil.util.AbstractVisitor;

/**
 * Translates WYIL bytecodes into Boogie and outputs into a given file.
 *
 * <b>NOTE:</b> the output file is put in the same place as the
 * Whiley file, but with the file extension ".bpl".  This file should
 * be sent to Boogie AFTER the WVal theory file: wval.bpl.
 *
 * <b>NOTE:</b> all values stored in records and arrays are Whiley values (Boogie type: WVal).
 * So if aa is a Whiley array of integers and ii is a Whiley integer (these are both WVal values),
 * we must write <pre>toArray(aa)</pre> to get the Boogie array value,
 * <pre>toArray(aa)[toInt(ii)]</pre> to get one entry out of the array,
 * and <pre>toInt(toArray(aa)[toInt(ii)]) == 1</pre> to compare that value with one.
 * See <pre>wval.bpl</pre> for the full model of WVal (Whiley values).
 *
 * DONE: generate in-context assertions for function preconditions, array bounds, etc.
 *
 * DONE: change do-while translation so that invariant is NOT checked before first iteration.
 *
 * DONE: improve assign to nested substructures - make it recursive.  (18 tests).
 *
 * DONE: refactor the BoogieExpr writeXXX() methods to boogieXXX().
 *
 * DONE: added generic equality axiom for records (to wval.bpl).
 *       Instead of generating equality axioms for each record type defined in Whiley.
 *
 * TODO: add type invariants to loops.  See While_Valid_62.whiley.
 *
 * TODO: refactor so that statements are returned as strings?
 *       This would allow us to use side-effects to declare local variables, refs, etc.
 *
 * TODO: add implicit conditions to each conjunct.  See Assert_Valid_1.whiley.
 *       ensures ys[0] == 0:  should be expanded to:  ensures 0<=0 && 0<|ys| && ys[0]==0:
 *       This needs a theory of three-valued logic for expressions?
 *
 * TODO: declare local variables for any missing output parameters of 'call' statements (see Array_Valid_9.whiley).

 * TODO: handle heap and references better.
 *       1. cleanup: generate ref__i variables only when necessary, or avoid them completely.
 *       2. pass w__heap as a parameter to methods that use the heap. (functions are not allowed to access heap!)
 *       3. add typing constraints for dereferenced values.
 *       4. strengthen the theory of heap updating and dereferencing.
 *
 * TODO: move ALL method calls out of expressions?  (5 tests do this!)
 *       See MethodCall_Valid_4.whiley for a complex example.
 *       See MethodRef_Valid_2.whiley for an example of indirect call of a method.
 *          (Could we handle this with an axiom that just asserts the ensures clause of the method?).
 *
 *
 * TODO: mangle Whiley var names to avoid Boogie reserved words and keywords.
 *       See Switch_Valid_5.whiley for an example where 'type' is used as a variable name.
 *       See While_Valid_42.whiley and ConstrainedList_Valid_23.whiley for quantifier variable same as local variable.
 *       See MethodRef_Valid_1.whiley for function name 'call'.
 *       See String_Valid_4.whiley for 'old' as a parameter name.
 *
 * TODO: generate assertions after each assignment, to check 'where' constraints?
 *       (Boogie checks 'where' constraints only in havoc statements, not for assignments).
 *
 * TODO: generate f(x)==e axiom for each Whiley function that is just 'return e'?
 *       (Because current translation only generates e into the __impl code of the function,
 *       so the semantics of the function are not visible elsewhere in the program.
 *       But this is a bit ad-hoc - the semantics should really be given in the postcondition!)
 *
 * TODO: implement missing language features, such as:
 * <ul>
 *   <li>DONE: Property declarations and uses.</li>
 *   <li>System.Console sys and sys.out.println(string)</li>
 *   <li>DONE: indirect invoke (12 tests)</li>
 *   <li>DONE: references, new (17 tests), and dereferencing (17 tests)</li>
 *   <li>DONE: switch (14 tests)</li>
 *   <li>DONE: lambda functions (17 tests)</li>
 *   <li>functions/methods with multiple return values (5 tests).  Need Boogie theory of tuples/arrays.</li>
 *   <li>DONE: continue statements and named blocks (3 tests)</li>
 *   <li>DONE (separate byte and int ops): bitwise operators (13 tests)</li>
 *   <li>DONE: generate type axioms for constants (tell Boogie the result of Whiley's type inference).</li>
 * </ul>
 *
 * @author David J. Pearce
 * @author Mark Utting
 */
@SuppressWarnings("StringConcatenationInsideStringBufferAppend")
public final class Wyil2Boogie {
	private static final boolean USE_BOOGIE_EQUALITY = true;

    /** Prefix for the function/method names namespace (the WFuncName Boogie type). */
    private static final String CONST_FUNC = "func__";

    private static final String HEAP = "w__heap";
    private static final String ALLOCATED = "w__alloc";
    private static final String NEW = "new";
    private static final String NEW_REF = "ref__";
    // max number of 'new' expressions in a single statement.
    // TODO: calculate this on the fly within each procedure?
    private static final int NEW_REF_MAX = 4;

    private static final String IMMUTABLE_INPUT = "__0";

    /** The conjunction operator for pre/post conditions. */
    private static final String AND_OUTER = " &&\n      ";

    /** This is appended to each function/method name, for the precondition of that function. */
    public static final String METHOD_PRE = "__pre";

    /** Where the Boogie output is written. */
	private final PrintWriter out;

    /**
     * If true, then the Whiley bytecodes are printed as comments.
     * Note: this must be set via the '-v' flag in the main method.
     */
	private boolean verbose = false;

    /** Keeps track of which (non-mangled) WField names have already been declared. */
    private final Set<String> declaredFields = new HashSet<>();

    /** Keeps track of which (non-mangled) function/method names have had their address taken. */
    private final Set<QualifiedName> referencedFunctions = new HashSet<>();

	/** Keeps track of a unique name for each lambda function. */
	private final Map<Decl.Lambda, String> lambdaFunctionName = new HashMap<>();

    /** Used to generate unique IDs for bound variables. */
    private int uniqueId = 0;

    /** Keeps track of the mangled names for every function and method. */
    private Map<String, Map<Type.Callable, String>> functionOverloads;

    /** Input parameters of the current function/method. */
	private Tuple<Decl.Variable> inDecls;

    /** Output parameters of the current function/method. */
	private Tuple<Decl.Variable> outDecls;

    /**
     * The method (procedure) that we are currently calling.
     *
     * Boogie syntax allows us to call a method (procedure) at the statement level only.
     * But method calls can appear ANYWHERE inside an 'executable' Whiley expression.
     * (they are not allowed in requires/ensures/assert/assume/inv expressions).
     * The current implementation of this translator only handles method calls
     * at the outermost level of an expression.
     * So while each statement is being translated, this variable points to
     * the outermost method, which is being 'called' (as a statement).
     * Any other method invocation inside the expression is illegal.
     * (Detecting them at this stage is better than generating illegal Boogie).
     * If this is null, then no outermost method is being called, so ALL
     * method invocations will be illegal.
     */
    private Expr outerMethodCall;

    /**
     * A stack of labels for the loops we are inside (innermost label last).
     *
     * These labels are prefixed by "CONTINUE__" at the start of the loop body,
     * and by "BREAK__" after the end of the whole loop statement.
     */
	private final Deque<String> loopLabels = new ArrayDeque<>();

	/** Increments with each loop we see, to allocate unique loop labels. */
	private int loopCounter;

    private final AssertionGenerator vcg;

    /**
	 * Used to generate unique labels for each switch statement.
	 * (This is separate from the loop counter because we allocate a local variable for each switch,
	 * and we need their names to be distinct.)
	 */
    private int switchCount;

    /** Records the values within all the 'new' expressions in the current statement. */
    private final List<String> newAllocations = new ArrayList<>();

	/** Records type synonyms, so we can unfold them during when generating equality tests. */
	private Map<String, Type> typeDefs = new HashMap<>();

	/**
	 * Responsible for extract concrete types (i.e. Type instances) from abstract
	 * types (i.e. SemanticType instances).
	 */
	private final ConcreteTypeExtractor concreteTypeExtractor;

	public Wyil2Boogie(PrintWriter writer) {
        this.out = writer;
        this.vcg = new AssertionGenerator(this);
        // Create concrete type extractor
        EmptinessTest<SemanticType> strictEmptiness = new StrictTypeEmptinessTest();
		this.concreteTypeExtractor = new ConcreteTypeExtractor(strictEmptiness);
    }

    public Wyil2Boogie(OutputStream stream) {
        this(new PrintWriter(new OutputStreamWriter(stream)));
    }


    // ======================================================================
    // Configuration Methods
    // ======================================================================

    public void setVerbose(boolean flag) {
        this.verbose = flag;
    }

    /**
     * Declare any new record fields that have not already been declared.
     *
     * This should be called with all fields in a definition, before that definition is output.
     */
	private void declareNewFields(Tuple<Type.Field> fields) {
		for (final Type.Field f : fields) {
			declareNewField(f.getName().get());
		}
	}

	private void declareNewField(String name) {
		if (!this.declaredFields.contains(name)) {
            this.out.println("const unique " + mangledWField(name) + ":WField;");
            this.declaredFields.add(name);
        }
	}

	/**
     * Declare any function or method names whose address is taken.
     *
     * This is careful to only declare a function the first time its name is seen.
     * So it is safe to call it on every function and method constant.
     */
	@SuppressWarnings("StringConcatenationInsideStringBufferAppend")
	private void declareHigherOrderFunction(QualifiedName name, Type.Callable type) {
        if (!this.referencedFunctions.contains(name)) {
        	// FIXME: this won't work for qualified names in packages (e.g. std::integer::u8)
            final String func_const = mangleFuncName(name);
            this.out.printf("const unique %s:WFuncName;\n", func_const);
            // At the moment, we assume indirect-invoke is used rarely, so for ONE type of function in each program.
            // TODO: extend this to handle more than one type of indirect-invoke result (different applyTo operators?)


			// TODO: change axioms from:
			// axiom (forall f:WVal, v1:WVal :: isFunction(f) ==> isInt(apply__1(toFunction(f), v1)));
			// axiom (forall v1:WVal, captured__:WVal :: apply__1(closure__1(func__f1, captured__), v1) == f1(v1));
			// to: (and check f_pre?)
			// axiom (forall v1..vn:WVal :: apply__1(closure__0(func__f1), v1..vn) == f1(v1..vn));

			if (type.getReturns().size() != 1) {
                throw new NotImplementedYet("multi-valued constant functions", null);
            }
            final Type ret = type.getReturns().get(0);
            final Tuple<Type> args = type.getParameters();
            final StringBuilder vDecl = new StringBuilder();
            final StringBuilder vCall = new StringBuilder();
            for (int i = 1; i <= args.size(); i++) {
                if (i > 1) {
                    vDecl.append(", ");
                    vCall.append(", ");
                }
                vDecl.append("v" + i + ":WVal");
                vCall.append("v" + i);
            }
            final String call = String.format("apply__%d(toFunction(f), %s)", args.size(), vCall.toString());
            // TODO: this is not needed now that all functions return WVal?
            this.out.printf("axiom (forall f:WVal, %s :: isFunction(f) ==> %s);\n",
					vDecl.toString(),
					typePredicate(call, ret));
            // TODO: we could handle different arities of captured variables here?
            this.out.printf("axiom (forall %s, captured__:WVal :: apply__%d(%s, %s) == %s(%s));\n\n",
                    vDecl.toString(),
					args.size(),
                    "closure__1(" + func_const + ", captured__)",
					vCall.toString(),
                    name.getName().toString(),
					vCall.toString());
            this.referencedFunctions.add(name);
        }
    }

	// ======================================================================
    // Apply Method
    // ======================================================================

    public void apply(WyilFile wf) {
    	Decl.Module module = wf.getModule();
    	// Iterate each locally declared compilation unit
    	for(Decl.Unit unit : module.getUnits()) {
    		apply(unit);
    	}
    	// FIXME: is this the right thing to do?
    	for(Decl.Unit unit : module.getExterns()) {
    		apply(unit);
    	}
    }

    private void apply(Decl.Unit unit) {
    	resolveFunctionOverloading(unit.getDeclarations());
		this.out.printf("var %s:[WRef]WVal;\n", HEAP);
		this.out.printf("var %s:[WRef]bool;\n", ALLOCATED);
		// TODO: find a nicer way of making these local?
		for (int i = 0; i < NEW_REF_MAX; i++) {
			this.out.printf("var %s%d : WRef;\n", NEW_REF, i);
		}
		this.out.println();
		for(final Decl decl : unit.getDeclarations()) {
			if (decl instanceof Decl.StaticVariable) {
				writeConstant((Decl.StaticVariable) decl);
			} else if (decl instanceof Decl.Type) {
				writeTypeSynonym((Decl.Type) decl);
				this.out.println();
				this.out.flush();
			} else if (decl instanceof Decl.FunctionOrMethod) {
				writeProcedure((Decl.FunctionOrMethod) decl);
				this.out.println();
				this.out.flush();
			} else if (decl instanceof Decl.Property) {
				writeProperty((Decl.Property) decl);
				this.out.println();
				this.out.flush();
			} else if (decl instanceof Decl.Import) {
				// skip
			} else {
				throw new NotImplementedYet("Unknown declaration " + decl.getClass(), decl);
			}
		}
    }
    /**
     * Whiley: <b>type</b> Name is (v:T) where P(v).
     * This is translated to Boogie as:
     * <pre>
     *   function isName(v:WVal) returns (bool) { isT(v) && P(v) };
     * </pre>
     *
     * @param td
     */
    private void writeTypeSynonym(Decl.Type td) {
        final Type t = td.getType();
        final Decl.Variable vd = td.getVariableDeclaration();
        declareFields(t, new HashSet<>());
		declareFields(td.getInvariant());
		declareFuncConstants(td.getInvariant());
		// writeModifiers(td.modifiers());
		String param = vd.getName().get();
		// NOTE: an unnamed parameter will be called '$', which works fine.
		this.out.printf("function %s(%s:WVal) returns (bool) {\n    ",
				typePredicateName(td.getName().get()),
				param);
		this.out.print(typePredicate(param, t));
		if (td.getInvariant().size() > 0) {
			this.out.print(AND_OUTER);
			writeConjunction(td.getInvariant());
		}
		this.out.println(" }");

		// remember this type synonym for later
		System.out.println("DEBUG: recording type " + td.getName().get() + " := " + t + " where " + td.getInvariant());
		this.typeDefs.put(td.getName().get(), t); // we do not need the invariants
	}

	private void writeConstant(Decl.StaticVariable cd) {
		declareFields(cd.getType(), new HashSet<>());
		declareFuncConstants(cd.getInitialiser());
		this.out.printf("const %s : WVal;\n", cd.getName());
		this.out.printf("axiom %s == %s;\n", cd.getName(), boogieExpr(cd.getInitialiser()).asWVal());
		final String typePred = typePredicate(cd.getName().get(), cd.getType());
		this.out.printf("axiom %s;\n\n", typePred);
	}

	/**
	 * Generates a Boogie procedure (and implementation) for the given Whiley
	 * function or method.
	 *
	 * We also generate a 'precondition function' called f__pre, which is true if
	 * the inputs satisfy all the typing conditions and preconditions of the
	 * function or method.
	 *
	 * For a function f, we generate a Boogie function f, as well as a procedure
	 * f_impl. The procedure is used to verify the code against pre/post. This is
	 * because Boogie functions cannot include code, they are uninterpreted
	 * functions or with an expression body only.
	 *
	 * The function encodes just the pre=>post properties, and is callable from
	 * parts of the specification.
	 *
	 * @param method
	 */
	private void writeProcedure(Decl.FunctionOrMethod method) {
		this.loopCounter = 0;
		final Type.Callable ft = method.getType();
		declareFields(method.getBody());
		declareFuncConstants(method.getBody());
		final String name = mangledFunctionMethodName(method.getName().get(), method.getType());
		final int inSize = ft.getParameters().size();
		final int outSize = ft.getReturns().size();
		this.inDecls = method.getParameters();
		this.outDecls = method.getReturns();
		assert this.inDecls.size() == inSize;
		assert this.outDecls.size() == outSize;
		if (outSize > 1) {
			throw new NotImplementedYet("multiple return values:" + name, null);
		}
		// define a function for the precondition of this method.
		writeMethodPre(name + METHOD_PRE, method, method.getRequires());
		String procedureName = name;
		if (method instanceof Decl.Function) {
			writeFunction(name, (Decl.Function) method);
			procedureName = name + "__impl";
		}
		this.out.print("procedure ");
		writeSignature(procedureName, method, null);
		this.out.println(";");
		this.out.printf("    modifies %s, %s;\n", HEAP, ALLOCATED);
		for (int i = 0; i < NEW_REF_MAX; i++) {
			this.out.printf("    modifies %s%d;\n", NEW_REF, i);
		}
		this.out.printf("    requires %s(%s);\n", name + METHOD_PRE, getNames(this.inDecls));
		// Part of the postcondition is the type and type constraints of each output
		// variable.
		//final Type[] outputs = method.type().returns();
		for (Decl.Variable locn : method.getReturns()) {
			final String inName = locn.getName().get();
			this.out.printf("    ensures %s;\n", typePredicate(inName, locn.getType()));
		}
		for (final Expr postcondition : method.getEnsures()) {
			this.out.printf("    ensures %s;\n", boogieBoolExpr(postcondition).toString());
		}
		final Map<String, Type> mutatedInputs = findMutatedInputs(method);
		this.out.print("implementation ");
		writeSignature(procedureName, method, mutatedInputs);
		if (method.getBody() != null) {
			this.out.println();
			this.out.println("{");
			writeLocalVarDecls(method.getBody());
			// now create a local copy of each mutated input!
			for (final String naughty : mutatedInputs.keySet()) {
				tabIndent(1);
				this.out.printf("var %s : WVal where ", naughty);
				this.out.print(typePredicate(naughty, mutatedInputs.get(naughty)));
				this.out.println(";");
			}
			// now assign the original inputs to the copies.
			for (final String naughty : mutatedInputs.keySet()) {
				tabIndent(1);
				this.out.printf("%s := %s;\n", naughty, naughty + IMMUTABLE_INPUT);
			}
			writeBlock(0, method.getBody());
			this.out.println("}");
		}
		this.inDecls = null;
		this.outDecls = null;
	}

	private Map<String, Type> findMutatedInputs(Decl.FunctionOrMethod method) {
		final Map<String, Type> result = new LinkedHashMap<>();
		final AbstractVisitor visitor = new AbstractVisitor() {
			@Override
			public void visitAssign(Stmt.Assign stmt) {
				for (Expr e : stmt.getLeftHandSide()) {
					boolean mayMutate = true; // guilty until proven innocent.
					while (!(e instanceof Expr.VariableAccess)) {
						if (e instanceof Expr.Dereference) {
							mayMutate = false;
							break;
						}
						// ArrayAccess, RecordAccess
						if (e instanceof Expr.RecordAccess) {
							e = ((Expr.RecordAccess) e).getOperand();
						} else if (e instanceof Expr.ArrayAccess) {
							e = ((Expr.ArrayAccess) e).getFirstOperand();
						} else {
							System.err.printf("WARNING: unknown assignment LHS: %s\n", e.toString());
						}
					}
					if (mayMutate) {
						Decl.Variable decl = ((Expr.VariableAccess) e).getVariableDeclaration();
						for (Decl.Variable param : method.getParameters()) {
							if (param == decl) {
								// this is a mutated input!
								final String name = decl.getName().get();
								System.err.printf("MUTATED INPUT %s : %s\n", name, decl.getType());
								result.put(name, decl.getType());
							}
						}
					}
				}
			}
		};
		visitor.visitBlock(method.getBody());
		return result;
	}

	private void writeMethodPre(String name, Decl.FunctionOrMethod method, Tuple<Expr> pre) {
		Tuple<Decl.Variable> parameters = method.getParameters();
		this.out.print("function ");
		this.out.print(name);
		this.out.print("(");
		writeParameters(parameters, null);
		this.out.print(") returns (bool)\n{\n      ");
		for (int i=0;i!=parameters.size();++i) {
			Decl.Variable parameter = parameters.get(i);
			if (i != 0) {
				this.out.print(AND_OUTER);
			}
			final String inName = parameter.getName().get();
			this.out.print(typePredicate(inName, parameter.getType()));
		}
		if (parameters.size() > 0) {
			this.out.print(AND_OUTER);
		}
		writeConjunction(pre);
		this.out.println("\n}");
	}

	/**
	 * Writes out a Whiley property declaration as a Boogie boolean function with explicit body.
	 *
	 * @param prop Whiley property
	 */
	private void writeProperty(Decl.Property prop) {
		final String name = mangledFunctionMethodName(prop.getName().get(), prop.getType());
		this.inDecls = prop.getParameters();
		this.outDecls = prop.getReturns();
		this.out.printf("function %s(", name);
		writeParameters(this.inDecls, null);
		this.out.println(") returns (bool);");

		// write axiom: (forall in :: f(in) <==> body);
		final String call = String.format("%s(%s)", name, getNames(this.inDecls));
		this.out.print("axiom (forall ");
		writeParameters(this.inDecls, null);
		this.out.printf(" :: {%s} %s <==> ", call, call);
		writeConjunction(prop.getInvariant());
		this.out.println(");");
		this.inDecls = null;
		this.outDecls = null;
	}

	/**
	 * Writes out a Boogie function declaration, plus a pre implies post axiom.
	 *
	 * @param name
	 *            the mangled name of the function
	 * @param method
	 *            all other details of the function
	 */
	private void writeFunction(String name, Decl.Function method) {
		Tuple<Decl.Variable> parameters = method.getParameters();
		Tuple<Decl.Variable> returns = method.getReturns();
		this.out.print("function ");
		this.out.print(name);
		this.out.print("(");
		writeParameters(parameters, null);
		if (returns.size() == 0) {
			this.out.println(");");
			throw new IllegalArgumentException("function with no return values: " + method);
		} else {
			this.out.print(") returns (");
			writeParameters(returns, null);
			this.out.println(");");

			// OLD: write axiom: (forall in,out :: f(in)==out && f_pre(in) ==> types(out) && post)
			// NEW: write axiom: (forall in :: {f(in)} f_pre(in) ==> (exists out :: types(out) && post))
			//    so that this axiom is triggered properly, each time we see f(...).
			final String inVars = getNames(this.inDecls);
			final String outVars = getNames(this.outDecls);
			if (parameters.size() == 0) {
				this.out.print("axiom ");
			} else {
				this.out.print("axiom (forall ");
				writeParameters(parameters, null);
				// trigger is f(in)
				this.out.printf(" :: {%s(%s)}\n    ", name, getNames(this.inDecls));
			}
			this.out.printf("%s(%s)\n",  name + METHOD_PRE, getNames(this.inDecls));
			this.out.print("    ==> (exists ");
			writeParameters(returns, null);
			this.out.printf(" ::\n        %s(%s) == (%s) &&\n        ", name, inVars, outVars);
			// Now write the type and type constraints of each output variable.
			for (int i = 0; i != returns.size(); ++i) {
				if (i != 0) {
					this.out.print(AND_OUTER);
				}
				final Decl.Variable outvar = returns.get(i);
				final String inName = outvar.getName().get();
				this.out.print(typePredicate(inName, outvar.getType()));
			}
			this.out.print(AND_OUTER);
			writeConjunction(method.getEnsures());
			if (parameters.size() == 0) {
				this.out.println(");");
			} else {
				this.out.println("));");
			}
		}
		this.out.println();
	}

	/**
	 * Get the names being declared.
	 *
	 * TODO: check if this also needs to rename mutated input variables?
	 *
	 * @param decls a list of declarations.
	 * @return a comma-separated string of just the names being declared.
	 */
	private String getNames(Tuple<Decl.Variable> decls) {
		final StringBuilder result = new StringBuilder();
		for (int i = 0; i != decls.size(); ++i) {
			if (i != 0) {
				result.append(", ");
			}
			final Decl.Variable locn = decls.get(i);
			result.append(locn.getName());
		}
		return result.toString();
	}

	/**
	 * Writes a conjunction, and leaves it as a Boogie boolean value.
	 *
	 */
	private void writeConjunction(Tuple<Expr> preds) {
		if (preds.size() == 0) {
			this.out.print("true");
		} else {
			String sep = "";
			for (final Expr pred : preds) {
				this.out.print(sep);
				sep = AND_OUTER;
				final BoogieExpr expr = boogieBoolExpr(pred);
				this.out.print(expr.withBrackets(" && ").toString());
			}
		}
	}

	private void writeSignature(String name, Decl.FunctionOrMethod method, Map<String, Type> mutatedInputs) {
		this.out.print(name);
		this.out.print("(");
		writeParameters(method.getParameters(), mutatedInputs);
		if (method.getReturns().size() > 0) {
			this.out.print(") returns (");
			writeParameters(method.getReturns(), null);
		}
		this.out.print(")");
	}

	/**
	 * Writes just the declarations and type constraints of local variables of a
	 * function/method.
	 *
	 * This is done only at the top level of each procedure. Boogie requires all
	 * local variables to be declared at the start of each function/procedure. So
	 * this writes out just one copy of each variable declaration. If a variable is
	 * declared more than once, with different types, then we cannot easily
	 * translate this to Boogie, so we throw an exception.
	 *
	 * It is hard to distinguish local variable declarations from bound variables
	 * inside quantifiers if we just do a linear scan of the Whiley bytecodes, so
	 * this method does a recursive descent through the code part of the function or
	 * method, looking for local variable declarations, and ignoring expressions and
	 * quantifiers.
	 *
	 * @param body
	 */
	private void writeLocalVarDecls(Stmt.Block body) {
		// We start after the input and output parameters.
		this.switchCount = 0;
		final Map<String, Type> locals = new LinkedHashMap<>(); // preserve order, but remove duplicates
		// Create visitor to traverse method or function body
		AbstractVisitor visitor = new AbstractVisitor() {
			@Override
			public void visitVariable(Decl.Variable decl) {
				final String name = decl.getName().get();
				final Type prevType = locals.get(name);
				if (prevType == null) {
					locals.put(name, decl.getType());
					tabIndent(1);
					out.printf("var %s : WVal where %s;\n", name, typePredicate(name, decl.getType()));
				} else if (!prevType.equals(decl.getType())) {
					throw new NotImplementedYet("local var " + name + " has multiple types", decl);
				}
			}
			@Override
			public void visitSwitch(Stmt.Switch decl) {
				switchCount++;
				tabIndent(1);
				// we don't bother recording these in the 'done' map, since each switch has a
				// unique variable.
				out.printf("var %s : WVal;\n", createSwitchVar(switchCount));
			}

			@Override
			public void visitExistentialQuantifier(Expr.ExistentialQuantifier expr) {
				// do not recurse in, because vars inside quantifiers are bound vars in Boogie.
			}

			@Override
			public void visitUniversalQuantifier(Expr.UniversalQuantifier expr) {
				// do not recurse in, because vars inside quantifiers are bound vars in Boogie.
			}
		};
		// Run the visitor
		visitor.visitBlock(body);
		// reset to zero so that we generate same numbers as we generate code.
		this.switchCount = 0;
	}

	/** A unique name for each switch statement within a procedure. */
	private String createSwitchVar(int count) {
		return "switch" + count + "__value";
	}

	private void writeParameters(Tuple<Decl.Variable> decls, Map<String, Type> rename) {
		for (int i = 0; i != decls.size(); ++i) {
			if (i != 0) {
				this.out.print(", ");
			}
			final Decl.Variable locn = decls.get(i);
			String name = locn.getName().get();
			if (rename != null && rename.containsKey(name)) {
				name = name + IMMUTABLE_INPUT;
			}
			this.out.print(name + ":WVal");
		}
	}

	private void writeBlock(int indent, Stmt.Block block) {
		for (int i = 0; i != block.size(); ++i) {
			writeStatement(indent, block.get(i));
		}
	}

	private void writeStatement(int indent, Stmt c) {
		tabIndent(indent + 1);
		switch (c.getOpcode()) {
		case STMT_assert: {
			Stmt.Assert s = (Stmt.Assert) c;
			this.vcg.checkPredicate(indent, s.getCondition());
			writeAssert(s); // should not contain 'new'
			break;
		}
		case STMT_assume: {
			Stmt.Assume s = (Stmt.Assume) c;
			this.vcg.checkPredicate(indent, s.getCondition());
			writeAssume(s); // should not contain 'new'
			break;
		}
		case STMT_assign: {
			Stmt.Assign s = (Stmt.Assign) c;
			final Tuple<LVal> lhs = s.getLeftHandSide();
			final Tuple<Expr> rhs = s.getRightHandSide();
			this.vcg.checkPredicates(indent, lhs);
			this.vcg.checkPredicates(indent, rhs);
			writeAssign(indent, s);
			break;
		}
		case STMT_break:
			writeBreak((Stmt.Break) c);
			break;
		case STMT_continue:
			writeContinue((Stmt.Continue) c);
			break;
		case STMT_debug:
			writeDebug((Stmt.Debug) c);
			break;
		case STMT_dowhile:
			writeDoWhile(indent, (Stmt.DoWhile) c);
			break;
		case STMT_fail:
			writeFail((Stmt.Fail) c);
			break;
		case STMT_if:
		case STMT_ifelse: {
			Stmt.IfElse s = (Stmt.IfElse) c;
			this.vcg.checkPredicate(indent, s.getCondition());
			writeIf(indent, s);
		}
			break;
		case EXPR_indirectinvoke:
			// TODO: check arguments against the precondition?
			this.out.print("call "); // it should be a method, not a function
			this.outerMethodCall = (Expr.IndirectInvoke) c;
			writeIndirectInvoke(indent, (Expr.IndirectInvoke) c);
			this.outerMethodCall = null;
			break;
		case EXPR_invoke:
			// TODO: check arguments against the precondition!
			this.out.print("call "); // it should be a method, not a function
			this.outerMethodCall = (Expr.Invoke) c;
			writeInvoke(indent, (Expr.Invoke) c);
			this.outerMethodCall = null;
			break;
		case STMT_namedblock:
			writeNamedBlock(indent, (Stmt.NamedBlock) c);
			break;
		case STMT_while: {
			Stmt.While s = (Stmt.While) c;
			this.vcg.checkPredicate(indent, s.getCondition());
			final Tuple<Expr> invars = s.getInvariant();
			this.vcg.checkPredicates(indent, invars);
			writeWhile(indent, s);
			break;
		}
		case STMT_return: {
			Stmt.Return s = (Stmt.Return) c;
			this.vcg.checkPredicates(indent, s.getReturns());
			writeReturn(indent, s);
			break;
		}
		case STMT_skip:
			writeSkip((Stmt.Skip) c);
			break;
		case STMT_switch: {
			Stmt.Switch s = (Stmt.Switch) c;
			this.vcg.checkPredicate(indent, s.getCondition());
			writeSwitch(indent, s);
			break;
		}
		case DECL_variableinitialiser: {
			Decl.Variable var = (Decl.Variable) c;
			this.vcg.checkPredicate(indent, var.getInitialiser());
			// fall through into the non-init case.
		}
		case DECL_variable: {
			Decl.Variable var = (Decl.Variable) c;
			// TODO: check the init expression
			writeVariableInit(indent, var);
			break;
		}
		case DECL_lambda:
			Decl.Lambda lambda = (Decl.Lambda) c;
			this.out.print("DECL lambda??" + boogieDeclLambda(lambda));
			break;

		default:
			throw new NotImplementedYet("unknown bytecode encountered", c);
		}
	}

	/**
	 * Generates a Boogie assertion to check the given conjecture.
	 *
	 * This is a helper function for AssertionGenerator.
	 *
	 * @param indent
	 * @param bndVars
	 * @param assumps
	 *            a list of predicates we can assume to prove the conjecture.
	 * @param conj
	 *            a Boolean Boogie expression.
	 */
	protected void generateAssertion(int indent, List<String> bndVars, List<BoogieExpr> assumps, BoogieExpr conj) {
		String close = ";";
		this.out.print("assert ");
		if (!bndVars.isEmpty()) {
			this.out.print("(forall ");
			close = ");";
			for (int i = 0; i < bndVars.size(); i++) {
				if (i > 0) {
					this.out.print(", ");
				}
				this.out.print(bndVars.get(i) + ":WVal");
			}
			this.out.print(" :: ");
		}
		for (int i = 0; i < assumps.size(); i++) {
			if (i > 0) {
				this.out.print("&& ");
			}
			this.out.println(assumps.get(i).as(BOOL).withBrackets(" && ").toString());
			tabIndent(indent + 2);
		}
		if (assumps.size() > 0) {
			this.out.print("==> ");
		}
		// finally, print the main assertion.
		this.out.print(conj.as(BOOL).withBrackets(" ==> ").toString());
		this.out.println(close);
		tabIndent(indent + 1); // get ready for next statement.
	}

	private void writeAssert(Stmt.Assert c) {
		this.out.printf("assert %s;\n", boogieBoolExpr(c.getCondition()).toString());
	}

	private void writeAssume(Stmt.Assume c) {
		this.out.printf("assume %s;\n", boogieBoolExpr(c.getCondition()).toString());
	}

	/**
	 * Generates code for an assignment statement.
	 *
	 * For assignments with complex LHS, like a[i], this always updates the whole
	 * structure. For example:
	 * <ol>
	 * <li>Instead of a[e] := rhs, we do a := a[e := rhs]; (see
	 * ListAssign_Valid_1.whiley)</li>
	 * <li>Instead of a.field := rhs, we do a := a[$field := rhs]; (see
	 * RecordAssign_Valid_1.whiley)</li>
	 * <li>Instead of a[e].field := rhs, we do a := a[e := a[e][field := rhs]]; (see
	 * Subtype_Valid_3.whiley)</li>
	 * <li>Instead of a.field[e] := rhs, we do a := a[$field := a[$field][e :=
	 * rhs]]; (see Complex_Valid_5.whiley)</li>
	 * <li>And so on, recursively, for deeper nested LHS.</li>
	 * <li>Instead of &a := rhs, we do heap := heap[a := rhs]; (see
	 * Reference_Valid_1.whiley)</li>
	 * <ol>
	 * In addition to the above, we have to add type conversions from WVal to array
	 * or record types, and back again.
	 *
	 * Calls the helper function <code>build_rhs()</code> to generate the complex
	 * RHS expressions.
	 *
	 * @param indent
	 * @param stmt
	 */
	private void writeAssign(int indent, Stmt.Assign stmt) {
		final Tuple<LVal> lhs = stmt.getLeftHandSide();
		final Tuple<Expr> rhs = stmt.getRightHandSide();
		// FIXME: not sure about this --- djp
		if (isMethod(rhs.get(0))) {
			this.outerMethodCall = rhs.get(0);
		}
		// first break down complex lhs terms, like a[i].f (into a base var and some indexes)
		final String[] lhsVars = new String[lhs.size()];
		@SuppressWarnings("unchecked")
		final List<Index>[] lhsIndexes = new List[lhs.size()];
		for (int i = 0; i != lhs.size(); ++i) {
			lhsIndexes[i] = new ArrayList<>();
			lhsVars[i] = extractLhsBase(lhs.get(i), lhsIndexes[i]);
		}
		// then build up any complex rhs terms, like a[i := (a[i][$f := ...])]
		final String[] rhsExprs = new String[rhs.size()];
		for (int i = 0; i != rhs.size(); ++i) {
			final String newValue = writeAllocations(indent, rhs.get(i)).asWVal().toString();
			rhsExprs[i] = build_rhs(lhsVars[i], lhsIndexes[i], 0, newValue);
		}

		// now start printing the assignment
		if (isMethod(rhs.get(0))) {
			// Boogie distinguishes method & function calls!
			this.out.print("call ");
			this.outerMethodCall = null;
		}
		for (int i = 0; i != lhsVars.length; ++i) {
			if (i != 0) {
				this.out.print(", ");
			}
			this.out.print(lhsVars[i]);
		}
		if (lhs.size() > 0) {
			final HashSet<String> noDups = new HashSet<>(Arrays.asList(lhsVars));
			if (noDups.size() < lhs.size()) {
				throw new NotImplementedYet("Conflicting LHS assignments not handled yet.", stmt);
			}
			this.out.print(" := ");
		}
		if (lhs.size() != rhs.size()) {
			if (Stream.of(lhsIndexes).anyMatch(x -> !x.isEmpty())) {
				throw new NotImplementedYet("Complex LHS vars in method call not handled yet.", stmt);
			}
			if (rhs.size() != 1) {
				throw new NotImplementedYet("Assignment with non-matching LHS and RHS lengths.", stmt);
			}
		}
		for (int i = 0; i != rhsExprs.length; ++i) {
			if (i != 0) {
				this.out.print(", ");
			}
			this.out.print(rhsExprs[i]);
		}
		this.out.println(";");
	}

	/**
	 * Updates the heap and allocated flags for any 'new' side-effects in expr. All
	 * expressions that could contain 'new' expressions should be processed via this
	 * method. It returns the resulting Boogie expression just like expr(...), but
	 * first updates the heap etc.
	 */
	private BoogieExpr writeAllocations(int indent, Expr expr) {
		this.newAllocations.clear();
		final BoogieExpr result = boogieExpr(expr);
		if (this.newAllocations.size() > 0) {
			String tab = ""; // first tab already done
			for (int i = 0; i < this.newAllocations.size(); i++) {
				final String ref = NEW_REF + i;
				this.out.printf("%s// allocate %s\n", tab, ref);
				tab = createIndent(indent + 1);
				this.out.printf("%s%s := %s(%s);\n", tab, ref, NEW, ALLOCATED);
				this.out.printf("%s%s := %s[%s := true];\n", tab, ALLOCATED, ALLOCATED, ref);
				this.out.printf("%s%s := %s[%s := %s];\n\n", tab, HEAP, HEAP, ref, this.newAllocations.get(i));
			}
			this.out.printf(tab);
			this.newAllocations.clear();
		}
		return result;
	}

	/** Some kind of index into a data structure. */
	private interface Index {
	}

	/** An index into an array. */
	private static class IntIndex implements Index {
		private final String index;

		private IntIndex(String i) {
			this.index = i;
		}

		@Override
		public String toString() {
			return "IntIndex(" + this.index + ")";
		}
	}

	/** An index into a given field within a record/object. */
	private static class FieldIndex implements Index {
		private final String field;

		private FieldIndex(String f) {
			this.field = f;
		}

		@Override
		public String toString() {
			return "FieldIndex(" + this.field + ")";
		}
	}

	/** An index into the heap (via a reference). */
	private static class DerefIndex implements Index {
		private final String ref;

		private DerefIndex(String ref) {
			this.ref = ref;
		}

		@Override
		public String toString() {
			return "DerefIndex(" + this.ref + ")";
		}
	}

	/**
	 * Extracts base variable that is being assigned to. Builds a list of all
	 * indexes into the 'indexes' list.
	 *
	 * TODO: wrap writeAllocations(indent, rhs[i]) around each expr(...) in case the
	 * indexes contain 'new' expressions!
	 *
	 * @param loc
	 *            the LHS expression AST.
	 * @param indexes
	 *            non-null list to append index bytecodes.
	 * @return null if LHS is not an assignment to a (possibly indexed) variable.
	 */
	private String extractLhsBase(LVal loc, List<Index> indexes) {
		if (loc instanceof Expr.ArrayAccess) {
			Expr.ArrayAccess e = (Expr.ArrayAccess) loc;
			final String indexStr = writeAllocations(0, e.getSecondOperand()).as(INT).toString();
			indexes.add(0, new IntIndex(indexStr));
			return extractLhsBase((LVal) e.getFirstOperand(), indexes);
		} else if (loc instanceof Expr.RecordAccess) {
			Expr.RecordAccess e = (Expr.RecordAccess) loc;
			final String field = e.getField().get();
			indexes.add(0, new FieldIndex(field));
			return extractLhsBase((LVal) e.getOperand(), indexes);
		} else if (loc instanceof Expr.Dereference) {
			Expr.Dereference e = (Expr.Dereference) loc;
			final String ref = boogieExpr(e.getOperand()).as(WREF).toString();
			indexes.add(0, new DerefIndex(ref));
			return HEAP;
		} else if (loc instanceof Expr.VariableAccess) {
			return boogieExpr(loc).asWVal().toString();
		}
		throw new NotImplementedYet("complex assignment left-hand side", loc);
	}

	/**
	 * Recursively builds a new RHS expression that updates one value inside a
	 * structure.
	 *
	 * @param wval_base
	 *            is the Boogie string form of the structure that must be updated.
	 * @param indexes
	 *            is the array of all the indexes into the value that must be
	 *            updated.
	 * @param pos
	 *            is which index (starting from 0) we are about to process.
	 * @param newValue
	 *            is the new value that must be assigned to the deepest part inside
	 *            the structure.
	 * @return a Boogie expression that will evaluate to the updated structure.
	 */
	private String build_rhs(final String wval_base, List<Index> indexes, int pos, String newValue) {
		final String result;
		if (pos == indexes.size()) {
			result = newValue;
		} else if (indexes.get(pos) instanceof IntIndex) {
			final String indexStr = ((IntIndex) indexes.get(pos)).index;
			// Instead of a[e] := rhs, we do a := a[e := rhs];
			final String a = "toArray(" + wval_base + ")";
			final String newWValBase = String.format("%s[%s]", a, indexStr);
			final String recValue = build_rhs(newWValBase, indexes, pos + 1, newValue);
			result = String.format("fromArray(%s[%s := %s], arraylen(%s))", a, indexStr, recValue, wval_base);
		} else if (indexes.get(pos) instanceof FieldIndex) {
			// Instead of a.field := rhs, we do a := a[$field := rhs];
			final String field = ((FieldIndex) indexes.get(pos)).field;
			final String r = "toRecord(" + wval_base + ")";
			final String newWValBase = String.format("%s[%s]", r, mangledWField(field));
			final String recValue = build_rhs(newWValBase, indexes, pos + 1, newValue);
			result = String.format("fromRecord(%s[%s := %s])", r, mangledWField(field), recValue);
		} else {
			if (pos != 0 || !wval_base.equals(HEAP)) {
				throw new NotImplementedYet("multiple levels of dereference := " + newValue, null);
			}
			final String ref = ((DerefIndex) indexes.get(pos)).ref;
			final String newWValBase = String.format("%s[%s]", HEAP, ref);
			final String recValue = build_rhs(newWValBase, indexes, pos + 1, newValue);
			result = String.format("%s[%s := %s]", HEAP, ref, recValue);
		}
		return result;
	}

	private boolean isMethod(Expr loc) {
		return (loc instanceof Expr.Invoke && ((Expr.Invoke) loc).getDeclaration() instanceof Decl.Method);
	}

	@SuppressWarnings("unused")
	private void writeBreak(Stmt.Break b) {
		this.out.printf("goto BREAK__%s;\n", this.loopLabels.getLast());
	}

	private void writeContinue(Stmt.Continue b) {
		if (this.loopLabels.getLast().startsWith("SWITCH")) {
			// TODO: implement 'continue' within switch.
			throw new NotImplementedYet("continue inside switch", b);
		}
		this.out.printf("goto CONTINUE__%s;\n", this.loopLabels.getLast());
	}

	@SuppressWarnings({"EmptyMethod", "unused"})
	private void writeDebug(Stmt.Debug b) {
		// out.println("debug;");
	}

	/**
	 * Generate Boogie code for do-while.
	 *
	 * NOTE: Boogie does not have a do{S}while(C) where I command, so we used to
	 * generate a while loop and use a boolean variable to force entry the first
	 * time. This allows break/continue statements to work with the body S. But this
	 * meant that the invariant was checked too soon (before whole loop).
	 *
	 * <pre>
	 *     do__while := true;
	 *     while (do__while || C) invar I { S; do__while := false; }
	 * </pre>
	 *
	 * So now we translate directly to Boogie if and goto label statements:
	 *
	 * <pre>
	 *     if (true) {
	 *         DO__WHILE__BODY:
	 *         S;
	 *         assert I;
	 *         if (C) { goto DO__WHILE__BODY; }
	 *     }
	 * </pre>
	 *
	 * @param indent
	 * @param b
	 */
	private void writeDoWhile(int indent, Stmt.DoWhile b) {
		final Tuple<Expr> loopInvariant = b.getInvariant();
		// Location<?>[] modifiedOperands = b.getOperandGroup(1);
		this.loopCounter++;
		this.loopLabels.addLast("DO__WHILE__" + this.loopCounter);
		// TODO: we could remove this if (true) {...} wrapper?
		this.out.printf("if (true) {\n");
		tabIndent(indent + 2);
		this.out.printf("CONTINUE__%s:\n", this.loopLabels.getLast());
		writeBlock(indent + 1, b.getBody());
		tabIndent(indent + 2);
		this.out.printf("// invariant:");
		this.vcg.checkPredicates(indent + 1, loopInvariant);
		writeLoopInvariant(indent + 2, "assert", loopInvariant);
		this.out.println();
		tabIndent(indent + 2);
		this.vcg.checkPredicate(indent + 1, b.getCondition());
		this.out.printf("// while:\n");
		tabIndent(indent + 2);
		final String cond = writeAllocations(indent, b.getCondition()).as(BOOL).toString();
		this.out.printf("if (%s) { goto CONTINUE__%s; }\n", cond, this.loopLabels.getLast());
		tabIndent(indent + 1);
		this.out.println("}");
		tabIndent(indent + 1);
		this.out.printf("BREAK__%s:\n", this.loopLabels.removeLast());
	}

	/**
	 * Whiley fail means this point in the code should be unreachable.
	 *
	 * In the refinement calculus, and Boogie, 'assert false' forces the verifier to
	 * check this.
	 *
	 * @param c
	 */
	private void writeFail(@SuppressWarnings("unused") Stmt.Fail c) {
		this.out.println("assert false;");
	}

	private void writeIf(int indent, Stmt.IfElse b) {
		final String cond = writeAllocations(indent, b.getCondition()).as(BOOL).toString();
		this.out.printf("if (%s) {\n", cond);
		writeBlock(indent + 1, b.getTrueBranch());
		if (b.hasFalseBranch()) {
			tabIndent(indent + 1);
			this.out.println("} else {");
			writeBlock(indent + 1, b.getFalseBranch());
		}
		tabIndent(indent + 1);
		this.out.println("}");
	}

	// TODO: decide how to encode indirect method calls
	private void writeIndirectInvoke(int indent, Expr.IndirectInvoke stmt) {
		final Tuple<Expr> arguments = stmt.getArguments();
		final String[] args = new String[arguments.size() + 1];
		args[0] = writeAllocations(indent, stmt.getSource()).as(METHOD).toString(); // and/or as(FUNC)??
		for (int i = 0; i != arguments.size(); ++i) {
			args[i + 1] = writeAllocations(indent, arguments.get(i)).asWVal().toString();
		}
		writeCall(args);
	}

	private void writeInvoke(int indent, Expr.Invoke stmt) {
		final Tuple<Expr> arguments = stmt.getOperands();
		final String[] args = new String[arguments.size() + 1];
		args[0] = mangledFunctionMethodName(stmt.getName().toString(), stmt.getDeclaration().getType());
		for (int i = 0; i != arguments.size(); ++i) {
			args[i + 1] = writeAllocations(indent, arguments.get(i)).asWVal().toString();
		}
		writeCall(args);
	}

	private void writeCall(String[] args) {
		this.out.printf("%s(", args[0]);
		for (int i = 1; i != args.length; ++i) {
			if (i != 1) {
				this.out.print(", ");
			}
			this.out.print(args[i]);
		}
		this.out.println(");");
	}

	// TODO: named block
	private void writeNamedBlock(int indent, Stmt.NamedBlock b) {
		this.out.print(b.getName());
		this.out.println(":");
		writeBlock(indent + 1, b.getBlock());
		throw new NotImplementedYet("named block", b);
	}

	private void writeWhile(int indent, Stmt.While b) {
		final Tuple<Expr> loopInvariant = b.getInvariant();
		// Location<?>[] modifiedOperands = b.getOperandGroup(1);
		final String cond = writeAllocations(indent, b.getCondition()).as(BOOL).toString();
		this.loopCounter++;
		this.loopLabels.addLast("WHILE__" + this.loopCounter);
		this.out.printf("CONTINUE__%s:\n", this.loopLabels.getLast());
		tabIndent(indent + 1);
		this.out.printf("while (%s)", cond);
		// out.print(" modifies ");
		// writeExpressions(modifiedOperands,out);
		writeLoopInvariant(indent + 2, "invariant", loopInvariant);
		this.out.println();
		tabIndent(indent + 1);
		this.out.println("{");
		writeBlock(indent + 1, b.getBody());
		tabIndent(indent + 1);
		this.out.println("}");
		tabIndent(indent + 1);
		this.out.printf("BREAK__%s:\n", this.loopLabels.removeLast());
	}

	private void writeLoopInvariant(int indent, String keyword, Tuple<Expr> loopInvariant) {
		if (loopInvariant.size() > 0) {
			for (final Expr clause : loopInvariant) {
				this.out.println();
				tabIndent(indent);
				this.out.printf("%s %s;", keyword, boogieBoolExpr(clause).toString());
			}
		}
	}

	private void writeReturn(int indent, Stmt.Return b) {
		// Boogie return does not take any expressions.
		// Instead, we must write to the result variables.
		final Tuple<Expr> operands = b.getReturns();
		final String[] args = new String[operands.size()];
		if (operands.size() == 1 && isMethod(operands.get(0))) {
			this.outerMethodCall = operands.get(0);
		}
		for (int i = 0; i != operands.size(); ++i) {
			args[i] = writeAllocations(indent, operands.get(i)).asWVal().toString();
		}
		if (operands.size() == 1 && isMethod(operands.get(0))) {
			this.out.print("call ");
			this.outerMethodCall = null;
		}
		for (int i = 0; i != operands.size(); ++i) {
			final Decl.Variable locn = this.outDecls.get(i);
			final String name = locn.getName().get();
			this.out.printf("%s := %s;\n", name, args[i]);
			tabIndent(indent + 1);
		}
		this.out.println("return;");
	}

	private void writeSkip(Stmt.Skip b) {
		// no output needed. Boogie uses {...} blocks, so empty statements are okay.
		this.out.println("// " + b);
	}

	/**
	 * Implements switch as a non-deterministic goto to all the cases.
	 *
	 * Cases are numbered, so that 'continue' can jump to the next case.
	 *
	 * TODO: handle continue in switch. (This just requires storing current case
	 * number i in a field, so can goto "SWITCH(n)__CASE(i+1)". But to support
	 * nested switches, we will need a stack of these case numbers!).
	 *
	 * @param indent
	 * @param sw
	 */
	private void writeSwitch(int indent, Stmt.Switch sw) {
		this.switchCount++;
		this.loopLabels.addLast("SWITCH" + this.switchCount);
		final String var = createSwitchVar(this.switchCount);
		final Tuple<Stmt.Case> cases = sw.getCases();
		final String value = writeAllocations(indent, sw.getCondition()).asWVal().toString();
		this.out.printf("%s := %s;\n", var, value);
		// build all the case labels we could jump to.
		final StringBuilder labels = new StringBuilder();
		for (int i = 0; i < cases.size(); i++) {
			if (i > 0) {
				labels.append(", ");
			}
			labels.append(this.loopLabels.getLast() + "__CASE" + i);
		}
		tabIndent(indent + 1);
		this.out.printf("goto %s;\n", labels.toString()); // non-deterministic
		final BoogieExpr defaultCond = new BoogieExpr(BoogieType.BOOL, "true");
		for (int i = 0; i < cases.size(); i++) {
			Stmt.Case cAse = cases.get(i);
			writeCase(indent + 1, var, i, cAse, defaultCond);
		}
		tabIndent(indent + 1);
		// We add a 'skip' statement after the BREAK label, just in case this switch is
		// not inside a block.
		// For example, Switch_Valid_5.whiley.
		this.out.printf("BREAK__%s:\n", this.loopLabels.removeLast());
	}

	/**
	 * Write one case (possibly with multiple values) and one block of code. This
	 * could be the default case, which will have zero values.
	 *
	 * @param indent
	 * @param varStr
	 *            the variable that contains the switch value
	 * @param count
	 *            the position (from zero) of the current case.
	 * @param c
	 *            the case matching values.
	 * @param defaultCond
	 *            a Boogie term that is the negation of all matching conditions so
	 *            far.
	 */
	private void writeCase(int indent, String varStr, int count, Stmt.Case c, BoogieExpr defaultCond) {
		// build the match condition: var == val1 || var == val2 || ...
		final BoogieExpr var = new BoogieExpr(BoogieType.WVAL, varStr);
		BoogieExpr match = new BoogieExpr(BoogieType.BOOL);
		String op = null;
		for (final Expr cd : c.getConditions()) {
			final BoogieExpr val = boogieExpr(cd).asWVal();
			final BoogieExpr test = new BoogieExpr(BoogieType.BOOL, var, " == ", val);
			final BoogieExpr negTest = new BoogieExpr(BoogieType.BOOL, var, " != ", val);
			defaultCond.addOp(" && ", negTest);
			if (op == null) {
				match = test;
			} else {
				match.addOp(op, test);
			}
			op = " || ";
		}
		tabIndent(indent + 1);
		this.out.printf(this.loopLabels.getLast() + "__CASE%d:\n", count);
		tabIndent(indent + 2);
		final BoogieExpr assume = c.getConditions().size() == 0 ? defaultCond : match;
		this.out.printf("assume %s;\n", assume.as(BOOL).toString());
		writeBlock(indent + 1, c.getBlock());
		tabIndent(indent + 2);
		this.out.printf("goto BREAK__%s;\n", this.loopLabels.getLast());
	}

	private void writeVariableInit(int indent, Decl.Variable loc) {
		if (loc.hasInitialiser()) {
			if (isMethod(loc.getInitialiser())) {
				this.outerMethodCall = loc.getInitialiser();
			}
			final BoogieExpr rhs = writeAllocations(indent, loc.getInitialiser()).asWVal();
			if (isMethod(loc.getInitialiser())) {
				this.out.printf("call ");
				this.outerMethodCall = null;
			}
			this.out.printf("%s := %s;\n", loc.getName(), rhs.toString());
		}
		// ELSE
		// TODO: Do we need a havoc here, to mimic non-det initialisation?
	}

	/** Convenience: equivalent to boogieExpr(_).as(BOOL). */
	BoogieExpr boogieBoolExpr(Expr expr) {
		return boogieExpr(expr).as(BOOL);
	}

	/** Convenience: equivalent to expr(_).as(INT). */
	BoogieExpr boogieIntExpr(Expr expr) {
		return boogieExpr(expr).as(INT);
	}

	@SuppressWarnings("unchecked")
	BoogieExpr boogieExpr(Expr expr) {
		switch (expr.getOpcode()) {
		case EXPR_arraylength:
			return boogieArrayLength((Expr.ArrayLength) expr);

		case EXPR_arrayaccess:
		case EXPR_arrayborrow:
			return boogieArrayIndex((Expr.ArrayAccess) expr);

		case EXPR_arrayinitialiser: {
			Expr.ArrayInitialiser e = (Expr.ArrayInitialiser) expr;
			final BoogieExpr[] avals = Arrays.stream(e.getOperands().toArray(Expr.class)).map(this::boogieExpr)
					.toArray(BoogieExpr[]::new);
			return createArrayInitialiser(avals);
		}
		case EXPR_arraygenerator:
			return boogieArrayGenerator((Expr.ArrayGenerator) expr);

		case EXPR_cast:
			return boogieConvert((Expr.Cast) expr);

		case EXPR_constant:
			final Expr.Constant c = (Expr.Constant) expr;
			return createConstant(c.getValue());

		case EXPR_recordborrow:
		case EXPR_recordaccess:
			return boogieFieldLoad((Expr.RecordAccess) expr);

		case EXPR_indirectinvoke:
			return boogieIndirectInvokeExpr((Expr.IndirectInvoke) expr);

		case EXPR_invoke:
			return boogieInvoke((Expr.Invoke) expr);

		case DECL_lambda:
			return boogieDeclLambda((Decl.Lambda) expr);

		case EXPR_lambdaaccess:
			return boogieLambda((Expr.LambdaAccess) expr);

		case EXPR_recordinitialiser: {
			Expr.RecordInitialiser e = (Expr.RecordInitialiser) expr;
			return createRecordConstructor(e);
		}
		case EXPR_new:
			return allocateNewObject((Expr.New) expr);

		case EXPR_dereference:
			return boogieDereference((Expr.Dereference) expr);

		case EXPR_logicalnot:
			return boogiePrefixOp(BOOL, (Expr.LogicalNot) expr, "! ", BOOL);

		case EXPR_integernegation:
			return boogiePrefixOp(INT, (Expr.IntegerNegation) expr, "- ", INT);

		case EXPR_logicaluniversal:
			return boogieQuantifier("forall", " ==> ", (Expr.UniversalQuantifier) expr);

		case EXPR_logicalexistential:
			return boogieQuantifier("exists", " && ", (Expr.ExistentialQuantifier) expr);

		case EXPR_integeraddition:
			return boogieInfixOp(INT, (Expr.IntegerAddition) expr, " + ", INT);

		case EXPR_integersubtraction:
			return boogieInfixOp(INT, (Expr.IntegerSubtraction) expr, " - ", INT);

		case EXPR_integermultiplication:
			return boogieInfixOp(INT, (Expr.IntegerMultiplication) expr, " * ", INT);

		case EXPR_integerdivision:
			// TODO: fix this for negative numbers.
			// Boogie 'mod' implements Euclidean division, whereas Whiley uses truncated
			// division.
			// See https://en.wikipedia.org/wiki/Modulo_operation for explanations.
			// See http://boogie.codeplex.com/discussions/397357 for what Boogie does.
			return boogieInfixOp(INT, (Expr.IntegerDivision) expr, " div ", INT);

		case EXPR_integerremainder:
			// TODO: fix this for negative numbers.
			// Boogie 'mod' implements Euclidean division, whereas Whiley uses truncated
			// division.
			// See https://en.wikipedia.org/wiki/Modulo_operation for explanations.
			// See http://boogie.codeplex.com/discussions/397357 for what Boogie does.
			return boogieInfixOp(INT, (Expr.IntegerRemainder) expr, " mod ", INT);

		case EXPR_bitwisenot: {
			Expr.BitwiseComplement e = (Expr.BitwiseComplement) expr;
			final String opType = getBitwiseType(e.getOperand());
			final BoogieExpr lhs = boogieExpr(e.getOperand()).as(INT);
			final String call = String.format("%s_invert(%s)", opType, lhs.toString());
			return new BoogieExpr(INT, call);
		}

		case EXPR_bitwiseor:
			return boogieBitwiseOp((Expr.BitwiseOr) expr, "or");
		case EXPR_bitwisexor:
			return boogieBitwiseOp((Expr.BitwiseXor) expr, "xor");
		case EXPR_bitwiseand:
			return boogieBitwiseOp((Expr.BitwiseAnd) expr, "and");
		case EXPR_bitwiseshl:
			return boogieBitwiseOp((Expr.BitwiseShiftLeft) expr, "shift_left");
		case EXPR_bitwiseshr:
			return boogieBitwiseOp((Expr.BitwiseShiftRight) expr, "shift_right");

		case EXPR_equal:
			return boogieEquality((Expr.Equal) expr);

		case EXPR_notequal:
			final BoogieExpr eq = boogieEquality((Expr.NotEqual) expr);
			final BoogieExpr outNE = new BoogieExpr(BOOL);
			outNE.addOp("! ", eq);
			return outNE;

		case EXPR_integerlessthan:
			return boogieInfixOp(INT, (Expr.IntegerLessThan) expr, " < ", BOOL);

		case EXPR_integerlessequal:
			return boogieInfixOp(INT, (Expr.IntegerLessThanOrEqual) expr, " <= ", BOOL);

		case EXPR_integergreaterthan:
			return boogieInfixOp(INT, (Expr.IntegerGreaterThan) expr, " > ", BOOL);

		case EXPR_integergreaterequal:
			return boogieInfixOp(INT, (Expr.IntegerGreaterThanOrEqual) expr, " >= ", BOOL);

		case EXPR_logicaland:
			return boogieInfixOp(BOOL, (Expr.LogicalAnd) expr, " && ", BOOL);

		case EXPR_logicalor:
			return boogieInfixOp(BOOL, (Expr.LogicalOr) expr, " || ", BOOL);

		case EXPR_logicaliff:
			return boogieEquality((Expr.BinaryOperator) expr);

		case EXPR_logiaclimplication:
			// we translate A ===> B into !A || B.
			final Expr.LogicalImplication impl = (Expr.LogicalImplication) expr;
			final BoogieExpr lhs = boogieExpr(impl.getFirstOperand()).as(BOOL);
			final BoogieExpr rhs = boogieExpr(impl.getSecondOperand()).as(BOOL);
			final BoogieExpr out1 = new BoogieExpr(BOOL);
			out1.addOp("! ", lhs);
			return new BoogieExpr(BOOL, out1, " || ", rhs);

		case EXPR_is:
			return boogieIs((Expr.Is) expr);

		case EXPR_variablecopy: // WAS: EXPR_varaccess:
		case EXPR_variablemove: // WAS: EXPR_varaccess:
			return boogieVariableAccess((Expr.VariableAccess) expr);

		case EXPR_staticvariable:
			Expr.StaticVariableAccess svar = (Expr.StaticVariableAccess) expr;
			// TODO? Decl.StaticVariable decl = typeSystem.resolveExactly(svar.getName(), Decl.StaticVariable.class);
			return new BoogieExpr(WVAL, svar.getName().getLast().toString());

		default:
			throw new IllegalArgumentException("unknown bytecode " + expr.getOpcode() + " encountered: " + expr);
		}
	}

	private BoogieExpr boogiePrefixOp(BoogieType argType, Expr.UnaryOperator c, String op, BoogieType resultType) {
		final BoogieExpr out = new BoogieExpr(resultType);
		final BoogieExpr rhs = boogieExpr(c.getOperand()).as(argType);
		out.addOp(op, rhs);
		return out;
	}

	private BoogieExpr boogieInfixOp(BoogieType argType, Expr.NaryOperator c, String op, BoogieType resultType) {
		Tuple<Expr> operands = c.getOperands();
		final BoogieExpr out = new BoogieExpr(resultType);
		final BoogieExpr lhs = boogieExpr(operands.get(0)).as(argType);
		final BoogieExpr rhs = boogieExpr(operands.get(1)).as(argType);
		out.addOp(lhs, op, rhs);
		return out;
	}

	private BoogieExpr boogieInfixOp(BoogieType argType, Expr.BinaryOperator c, String op, BoogieType resultType) {
		final BoogieExpr out = new BoogieExpr(resultType);
		final BoogieExpr lhs = boogieExpr(c.getFirstOperand()).as(argType);
		final BoogieExpr rhs = boogieExpr(c.getSecondOperand()).as(argType);
		out.addOp(lhs, op, rhs);
		return out;
	}

	private BoogieExpr boogieBitwiseOp(Expr.NaryOperator c, String op) {
		Tuple<Expr> operands = c.getOperands();
		final String opType = getBitwiseType(operands.get(0));
		final BoogieExpr lhs = boogieExpr(operands.get(0)).as(INT);
		final BoogieExpr rhs = boogieExpr(operands.get(1)).as(INT);
		final String call = String.format("%s_%s(%s, %s)", opType, op, lhs.toString(), rhs.toString());
		return new BoogieExpr(INT, call);
	}

	private BoogieExpr boogieBitwiseOp(Expr.BinaryOperator c, String op) {
		final String opType = getBitwiseType(c.getFirstOperand());
		final BoogieExpr lhs = boogieExpr(c.getFirstOperand()).as(INT);
		final BoogieExpr rhs = boogieExpr(c.getSecondOperand()).as(INT);
		final String call = String.format("%s_%s(%s, %s)", opType, op, lhs.toString(), rhs.toString());
		return new BoogieExpr(INT, call);
	}

	/** We distinguish bitwise operators on byte values from other int values. */
	private String getBitwiseType(Expr operand) {
		return operand.getType().equals(Type.Byte) ? "byte" : "bitwise";
	}

	private BoogieExpr boogieVariableAccess(Expr.VariableAccess loc) {
		final Decl.Variable vd = loc.getVariableDeclaration();
		final String name = vd.getName().get();
		return new BoogieExpr(WVAL, name);
	}

	private BoogieExpr boogieArrayLength(Expr.ArrayLength expr) {
		final BoogieExpr out = new BoogieExpr(INT);
		out.append("arraylen(");
		out.addExpr(boogieExpr(expr.getOperand()).asWVal());
		out.append(")");
		return out;
	}

	private BoogieExpr boogieArrayIndex(Expr.ArrayAccess expr) {
		final BoogieExpr out = new BoogieExpr(WVAL);
		out.addExpr(boogieExpr(expr.getFirstOperand()).as(ARRAY));
		out.addOp("[", boogieIntExpr(expr.getSecondOperand()));
		out.append("]");
		return out;
	}

	/**
	 * Whiley array generators [val;len] are represented as:
	 *
	 * <pre>
	 * fromArray(arrayconst(val), len)
	 * </pre>
	 *
	 * @param expr
	 */
	private BoogieExpr boogieArrayGenerator(Expr.ArrayGenerator expr) {
		final BoogieExpr out = new BoogieExpr(WVAL);
		out.append("fromArray(arrayconst(");
		out.addExpr(boogieExpr(expr.getFirstOperand()).asWVal());
		out.append("), ");
		out.addExpr(boogieExpr(expr.getSecondOperand()).as(INT));
		out.append(")");
		return out;
	}

	private BoogieExpr boogieConvert(Expr.Cast expr) {
		// TODO: implement the record (and object?) conversion that drops fields?
		// See tests/valid/Coercion_Valid_9.whiley
		// TODO: are there any valid conversions in Boogie?
		// out.print("(" + expr.getType() + ") ");
		return boogieExpr(expr.getOperand());
	}

	private BoogieExpr boogieFieldLoad(Expr.RecordAccess expr) {
		final BoogieExpr out = new BoogieExpr(WVAL);
		out.addExpr(boogieExpr(expr.getOperand()).as(RECORD));
		out.appendf("[%s]", mangledWField(expr.getField().get()));
		return out;
	}

	private BoogieExpr boogieInvoke(Expr.Invoke expr) {
		// TODO: check that it is safe to use unqualified DeclID names?
		BoogieType outType = WVAL;
		final String name = expr.getName().toString();
		final Type.Callable type = expr.getDeclaration().getType();
		if (type instanceof Type.Method) {
			if (expr != this.outerMethodCall) {
				// The Whiley language spec 0.3.38, Section 3.5.5, says that because they are
				// impure, methods cannot be called inside specifications.
				throw new NotImplementedYet("call to method (" + name + ") from inside an expression", expr);
			}
		} else if (type instanceof Type.Property) {
			outType = BOOL; // properties are translated to Boogie boolean functions.
		}
		final BoogieExpr out = new BoogieExpr(outType);
		out.append(mangledFunctionMethodName(name, type) + "(");
		final Tuple<Expr> operands = expr.getOperands();
		for (int i = 0; i != operands.size(); ++i) {
			if (i != 0) {
				out.append(", ");
			}
			out.addExpr(boogieExpr(operands.get(i)).asWVal());
		}
		out.append(")");
		return out;
	}

	private BoogieExpr boogieIndirectInvokeExpr(Expr.IndirectInvoke expr) {
		final Tuple<Expr> args = expr.getArguments();
		if (args.size() != 1) {
			throw new NotImplementedYet("indirect invoke with " + args.size() + " args", expr);
		}
		final BoogieExpr func = boogieExpr(expr.getSource()).as(FUNCTION);
		// FIXME: this doesn't seem right --- djp
		final BoogieExpr arg = boogieExpr(args.get(0)).asWVal();
		// TODO: decide what to do if func is a method?
		return new BoogieExpr(WVAL, "apply__1(" + func + ", " + arg + ")");
	}

	/**
	 * Ourput a lambda function as a closure.
	 *
	 * @param lambda the lambda function, which may capture surrounding variables.
	 * @return a Boogie Closure expression.
	 */
	private BoogieExpr boogieDeclLambda(Decl.Lambda lambda) {
		System.out.println("DECL_lambda:"
				+ "\n  name     : " + lambda.getName() // usually empty string
				+ "\n  captures : " + lambda.getCapturedVariables() // Set<Variable>
				+ "\n  type     : " + lambda.getType()
				+ "\n  types    : " + lambda.getTypes() // always null
				+ "\n  params   : " + lambda.getParameters()
				+ "\n  body    : " + lambda.getBody()  // an Expr
				+ "\n  returns : " + lambda.getReturns()
				+ "\n  string  : " + lambda.toString()
		);
		String lambdaName = this.lambdaFunctionName.get(lambda);
		if (lambdaName == null) {
			throw new IllegalStateException("missed lambda on pass 1: " + lambda);
		}
		Set<Decl.Variable> captures = lambda.getCapturedVariables();
		StringBuilder closure = new StringBuilder();
		closure.append("closure__");
		closure.append(captures.size());
		closure.append("(");
		closure.append(lambdaName);
		// NOTE: assumes that lambda.getCapturedVariables() always returns the same set with the same iteration order.
		for (Decl.Variable v : captures) {
			closure.append(", ");
			closure.append(v.getName().get());
		}
		closure.append(")");
		return new BoogieExpr(BoogieType.FUNCTION, closure.toString());
	}

	/**
	 * See Lambda_Valid_9.whiley and FunctionRef_Valid_1.whiley for examples that use these.
	 *
	 * @param lambda
	 * @return
	 */
	private BoogieExpr boogieLambda(Expr.LambdaAccess lambda) {
		// FIXME: encoding will be required for package declarations, such as
		// "std::integer::u8"
		QualifiedName name = lambda.getDeclaration().getQualifiedName();
		final String func_const = mangleFuncName(name);
		System.out.println("DEBUG: Expr.LambdaAccess:"
				+ "\n  name     : " + lambda.getName()
				+ "\n  paraTypes: " + lambda.getParameterTypes()
				+ "\n  signature: " + lambda.getDeclaration().getType()
				+ "\n  type     : " + lambda.getType()
				+ "\n  types    : " + lambda.getTypes()
				+ "\n  data    : " + Arrays.toString(lambda.getData())
				+ "\n  string  : " + lambda.toString()
		);
		return new BoogieExpr(BoogieType.FUNCTION, "closure__0(" + func_const + ")");
	}

	/**
	 * Sets up a heap allocation and returns the result heap reference as an
	 * expression.
	 *
	 * @param expr
	 * @return a freshly allocated heap reference.
	 */
	private BoogieExpr allocateNewObject(Expr.New expr) {
		final BoogieExpr be = boogieExpr(expr.getOperand()).asWVal();
		final String ref = NEW_REF + this.newAllocations.size();
		// this allocation will be done just BEFORE this expression
		this.newAllocations.add(be.toString());
		return new BoogieExpr(WREF, ref);
	}

	private BoogieExpr boogieDereference(Expr.Dereference expr) {
		final BoogieExpr be = boogieExpr(expr.getOperand()).as(WREF);
		// TODO: assume the type information of out.
		return new BoogieExpr(WVAL, "w__heap[" + be.toString() + "]");
	}

	private BoogieExpr boogieIs(Expr.Is c) {
		final Expr lhs = c.getOperand();
		final Type rhs = c.getTestType();
		// convert lhs to a string, so we can pass it into typePredicate(...).
		final String lhsStr = boogieExpr(lhs).as(WVAL).asAtom().toString();
		BoogieExpr typePred = new BoogieExpr(BOOL, typePredicate(lhsStr, rhs));
		typePred.setOp(" && ");
		return typePred;
	}

	/**
	 * Equality and inequality requires type-dependent expansion.
	 *
	 * @param c a binary equality or inequality expression.
	 */
	private BoogieExpr boogieEquality(Expr.BinaryOperator c) {
		final Expr left = c.getFirstOperand();
		final Expr right = c.getSecondOperand();
		if (USE_BOOGIE_EQUALITY) {
			// with this approach we just directly use Boogie equality.
			final BoogieExpr out = new BoogieExpr(BOOL);
			out.addOp(boogieExpr(left).asWVal(), " == ", boogieExpr(right).asWVal());
			return out;
		} else {
			final Type leftType = left.getType();
			final Type rightType = right.getType();
			// try to find a simple intersection of leftType and rightType
			SemanticType intersectType = new SemanticType.Intersection(leftType, rightType);
			// FIXME: using null for LifetimeRelation will not work for references types. To
			// resolve this, you'll need to pass a LifetimeRelation down through the
			// statements and expressions of each method. See FlowTypeChecker for how to do
			// this.
			Type usableType = concreteTypeExtractor.apply(intersectType, null);
			// finally, generate an appropriate equality check for this intersection type
			return boogieTypedEquality(usableType, boogieExpr(left), boogieExpr(right)).as(BOOL);
		}
	}

	/** True for the types that our equality code generator can handle. */
	private Type findUsableEqualityType(SemanticType type) {
		final String str = type.toString();
		if (str.equals("bool") // WAS type instanceof Type.Bool
				|| str.equals("int") // WAS type instanceof Type.Int
				|| str.equals("byte") // WAS type instanceof Type.Byte
				|| str.equals("null") // WAS type instanceof Type.Null
				) {
			return (Type) type;
		} else if (type instanceof Type.Array) {
			Type.Array aType = (Type.Array) type;
			Type elemType = findUsableEqualityType(aType.getElement());
			return elemType == null ? null : new Type.Array(elemType);
		} else if (type instanceof Type.Record) {
			Type.Record aType = (Type.Record) type;
			// Now we map all the field types too!
			List<Type.Field> fields = new ArrayList<>();
			for (Type.Field v : aType.getFields()) {
				Type fType = findUsableEqualityType(v.getType());
				if (fType == null) {
					return null; // give up!
				}
				fields.add(new Type.Field(v.getName(), fType));
			}
			return new Type.Record(aType.isOpen(), new Tuple(fields));
		} else if (type instanceof Type.Intersection) {
			Type.Intersection aType = (Type.Intersection) type;
			for (int i = 0; i < aType.size(); i++) {
				Type result = findUsableEqualityType(aType.get(i));
				if (result != null) {
					return result;
				}
			}
			// System.out.println("DEBUG: equality intersection null: " + type);
			return null;
		} else if (type instanceof Type.Difference) {
			Type.Difference aType = (Type.Difference) type;
			return findUsableEqualityType(aType.getLeftHandSide());
		} else if (type instanceof Type.Nominal) {
			Type.Nominal aType = (Type.Nominal) type;
			Type result = this.typeDefs.getOrDefault(aType.getName().get(0).get(), null);
			// System.out.println("DEBUG: unfold eq type: " + type + " -> " + result);
			return findUsableEqualityType(result);
		} else {
			System.out.println("DEBUG: difficult equality type: " + type);
			return null;
		}
	}

	/**
	 * A recursive helper function for writeEquality.
	 *
	 * @param eqType
	 *            both left and right must belong to this type for the equality to
	 *            be true.
	 * @param left
	 *            the LHS expression
	 * @param right
	 *            the RHS expression
	 */
	private BoogieExpr boogieTypedEquality(Type eqType, BoogieExpr left, BoogieExpr right) {
		final BoogieExpr out = new BoogieExpr(BOOL);
		final String eqTypeStr = eqType.toString();
		if (eqTypeStr.equals("null")) {
			// This requires special handling, since we do not have toNull and fromNull
			// functions.
			// Instead, we just compare both sides to the WVal 'null' constant.
			// TODO: an alternative would be to just compare the WVals using '=='?
			final BoogieExpr nulle = new BoogieExpr(NULL, "null");
			final BoogieExpr lhs = new BoogieExpr(BOOL, left.asWVal(), " == ", nulle);
			final BoogieExpr rhs = new BoogieExpr(BOOL, right.asWVal(), " == ", nulle);
			out.addOp(lhs, " && ", rhs);
		} else if (eqTypeStr.equals("int") // WAS eqType instanceof Type.Int
				|| eqTypeStr.equals("byte")) { // WAS eqType instanceof Type.Byte) {
			out.addOp(left.as(INT), " == ", right.as(INT));
		} else if (eqTypeStr.equals("bool")) { // WAS eqType instanceof Type.Bool) {
			out.addOp(left.as(BOOL), " == ", right.as(BOOL));
		} else if (eqType instanceof Type.Record) {
			final BoogieExpr leftRec = left.as(RECORD).asAtom();
			final BoogieExpr rightRec = right.as(RECORD).asAtom();
			final Type.Record recType = (Type.Record) eqType;
			final Decl.Variable[] fields = recType.getFields().toArray(Decl.Variable.class);
			Arrays.sort(fields, fieldsComparator);
			if (fields.length == 0) {
				out.append("true");
			}
			for (int i = 0; i < fields.length; i++) {
				final Decl.Variable field = fields[i];
				final String deref = "[" + mangledWField(field.getName().get()) + "]";
				final BoogieExpr leftVal = new BoogieExpr(WVAL, leftRec + deref);
				final BoogieExpr rightVal = new BoogieExpr(WVAL, rightRec + deref);
				final BoogieExpr feq = boogieTypedEquality(field.getType(), leftVal, rightVal).as(BOOL);
				if (i == 0) {
					out.addExpr(feq);
				} else {
					out.addOp(" && ", feq);
				}
			}
		} else if (eqType instanceof Type.Array) {
			final BoogieExpr leftArray = left.as(ARRAY).asAtom();
			final BoogieExpr rightArray = right.as(ARRAY).asAtom();
			final Type.Array arrayType = (Type.Array) eqType;
			final Type elemType = arrayType.getElement();
			// we check the length and all the values:
			// arraylen(left) == arraylen(right)
			// && (forall i:int :: 0 <= i && i < arraylen(a) ==> left[i] == right[i])
			final String index = generateFreshBoundVar("idx");
			final String deref = "[" + index + "]";
			final BoogieExpr leftVal = new BoogieExpr(WVAL, leftArray + deref);
			final BoogieExpr rightVal = new BoogieExpr(WVAL, rightArray + deref);
			out.appendf("arraylen(%s) == arraylen(%s) && (forall %s:int :: 0 <= %s && %s < arraylen(%s)",
					left.asWVal().toString(), right.asWVal().toString(), index, index, index, left.asWVal().toString());
			out.addOp(" ==> ", boogieTypedEquality(elemType, leftVal, rightVal).as(BOOL));
			out.append(")");
			out.setOp(" && "); // && is outermost, since the ==> is bracketed.
		} else {
			throw new NotImplementedYet(
					"comparison of values of type: " + eqType + ".  " + left.toString() + " == " + right.toString(),
					null);
		}
		return out;
	}

	private static final Comparator<Decl.Variable> fieldsComparator = Comparator.comparing(Decl.Named::getName);

	@SuppressWarnings("unchecked")
	private BoogieExpr boogieQuantifier(String quant, String predOp, Expr.Quantifier c) {
		final BoogieExpr decls = new BoogieExpr(BOOL);
		final BoogieExpr constraints = new BoogieExpr(BOOL);
		Tuple<Decl.Variable> parameters = c.getParameters();
		for (int i = 0; i != parameters.size(); ++i) {
			Decl.Variable parameter = parameters.get(i);
			Expr.ArrayRange range = (Expr.ArrayRange) parameter.getInitialiser();
			if (i != 0) {
				decls.append(", ");
				constraints.append(" && ");
			}
			// declare the bound variable: v:WVal
			final String name = parameter.getName().get();
			decls.appendf("%s:WVal", name);

			// and add the constraint: isInt(v) && start <= v && v <= end
			final BoogieExpr vExpr = new BoogieExpr(WVAL, name).as(INT);
			final BoogieExpr start = boogieIntExpr(range.getFirstOperand());
			final BoogieExpr end = boogieIntExpr(range.getSecondOperand());
			constraints.append("isInt(" + name + ")");
			constraints.addOp(" && ", new BoogieExpr(BOOL, start, " <= ", vExpr));
			constraints.addOp(" && ", new BoogieExpr(BOOL, vExpr, " < ", end));
		}
		final BoogieExpr out = new BoogieExpr(BOOL);
		out.appendf("(%s %s :: ", quant, decls.toString());
		out.addOp(constraints, predOp, boogieBoolExpr(c.getOperand()));
		out.append(")");
		return out;
	}

	/**
	 * Writes the given indentation levels into the output.
	 *
	 * @param indent
	 */
	private void tabIndent(int indent) {
		indent = indent * 4;
		for (int i = 0; i < indent; ++i) {
			this.out.print(" ");
		}
	}

	/** Returns an indent of the requested number of 'tab' stops. */
	String createIndent(int indent) {
		return indent <= 0 ? "" : String.format("%" + (indent * 4) + "s", "");
	}

	/**
	 * Translate the WyIL type into the type in Boogie.
	 *
	 * @param var
	 *            the name of the variable being typed. Example "a".
	 * @param type
	 *            the WyIL type
	 * @return a Boogie boolean typing predicate, such as "isInt(a)". The outermost
	 *         operator will have precedence of && or tighter.
	 */
	private String typePredicate(String var, Type type) {
		final String typeStr = type.toString();
		if (type instanceof Type.Nominal) {
			final String typeName = ((Type.Nominal) type).getName().toString();
			return typePredicateName(typeName) + "(" + var + ")";
		}
		if (typeStr.equals("int")) { // WAS type instanceof Type.Int) {
			return "isInt(" + var + ")";
		}
		if (typeStr.equals("byte")) { // WAS type instanceof Type.Byte) {
			return "isByte(" + var + ")";
		}
		if (typeStr.equals("null")) { // WAS type instanceof Type.Null) {
			return "isNull(" + var + ")";
		}
		if (typeStr.equals("bool")) { // WAS type instanceof Type.Bool) {
			return "isBool(" + var + ")";
		}
		if (typeStr.equals("any")) { // WAS type instanceof Type.Any) {
			return "true";
		}
		if (type instanceof Type.Array) {
			final Type.Array t = (Type.Array) type;
			final Type elemType = t.getElement();
			final String bndVar = generateFreshBoundVar("i__");
			final String elem = "toArray(" + var + ")[" + bndVar + "]";
			return String.format("isArray(%s) && (forall %s:int :: 0 <= %s && %s < arraylen(%s) ==> %s)", var, bndVar,
					bndVar, bndVar, var, typePredicate(elem, elemType));
		}
		// if (type instanceof Type.Void) {
		// // this should not happen?
		// }
		if (type instanceof Type.Record) {
			final Type.Record t = (Type.Record) type;
			// WAS final Map<String, Type> fields = t.fields();
			final Tuple<Type.Field> fields = t.getFields();
			// add constraints about the fields
			final String objrec;
			// if (t.isOpen()) {
			// objrec = "Object(" + var + ")";
			// } else {
			objrec = "Record(" + var + ")";
			// }
			final StringBuilder result = new StringBuilder();
			result.append("is" + objrec);
			// WAS for (final Map.Entry<String, Type> field : fields.entrySet()) {
			for (final Type.Field field : fields) {
				result.append(" && ");
				final String elem = "to" + objrec + "[" + mangledWField(field.getName().get()) + "]";
				final Type elemType = field.getType();
				result.append(typePredicate(elem, elemType));
			}
			return result.toString();
		}
		if (type instanceof Type.Union) {
			// we generate the disjunction of all the bounds
			final Type.Union u = (Type.Union) type;
			final StringBuilder sb = new StringBuilder();
			sb.append("((");
			String sep = "";
			for (int i = 0; i != u.size(); ++i) {
				sb.append(sep);
				sb.append(typePredicate(var, u.get(i)));
				sep = ") || (";
			}
			sb.append("))");
			return sb.toString();
		}
		if (type instanceof Type.Reference) {
			// TODO: add typing of dereference element, once we pass w__heap into functions.
			// Type.Reference ref = (Type.Reference) type;
			// String deref = "w__heap[toRef(" + var + ")]";
			return "isRef(" + var + ")"; // && " + typePredicate(deref, ref.getElement());
		}
		if (type instanceof Type.Function) {
			// TODO: add input and output types.
			return "isFunction(" + var + ")";
		}
		if (type instanceof Type.Method) {
			// TODO: add input and output types.
			return "isMethod(" + var + ")";
		}
		throw new NotImplementedYet("type: " + type, null);
	}

	/**
	 * Create a user-defined type predicate name, like "is_list", from a type name
	 * "list".
	 *
	 * Note: we add the underscore to avoid name clashes with some of the predefined
	 * predicates, like isInt(_).
	 *
	 * @param typeName
	 *            a non-empty string.
	 * @return a non-null string.
	 */
	private String typePredicateName(String typeName) {
		return "is_" + typeName;
	}

	/**
	 * Given a constant of the given type, cast it into a WVal value.
	 *
	 * @param cd
	 *            a Whiley constant, with a type.
	 * @return an expression string with type WVal.
	 */
	private BoogieExpr createConstant(Value cd) {
		if (cd instanceof Value.Int) {
			return new BoogieExpr(INT, cd.toString());
		} else if (cd instanceof Value.Bool) {
			return new BoogieExpr(BOOL, cd.toString());
		} else if (cd instanceof Value.Byte) {
			final Value.Byte b = (Value.Byte) cd;
			final int val = Byte.toUnsignedInt(b.get());
			return new BoogieExpr(INT, Integer.toString(val));
		} else if (cd instanceof Value.Null) {
			return new BoogieExpr(WVAL, "null"); // already a WVal;
		} else if (cd instanceof Value.UTF8) {
			// we turn the string into an array of ints.
			final String str = cd.toString();
			int len = 0;
			final StringBuilder sb = new StringBuilder();
			sb.append("arrayconst(fromInt(0))");
			for (int i = 0; i < str.length(); len++) {
				int cp = str.codePointAt(i);
				sb.append("[" + len + " := fromInt(" + cp + ")]");
				i += Character.charCount(cp);
			}
			return new BoogieExpr(WVAL, "fromArray(" + sb.toString() + ", " + len + ")");
		} else {
			throw new NotImplementedYet("createConstant(" + cd + ")", null);
		}
	}

	/**
	 * Whiley array literals [a,b,c] (and strings) are represented as:
	 *
	 * <pre>
	 *   fromArray(arrayconst(a)[1 := b][2 := c], 3)
	 * </pre>
	 *
	 * @param values
	 *            the expressions that initialise the array.
	 * @return
	 */
	private BoogieExpr createArrayInitialiser(BoogieExpr[] values) {
		final BoogieExpr out = new BoogieExpr(WVAL);
		out.append("fromArray(arrayconst(");
		if (values.length == 0) {
			out.append("null"); // the type of values should be irrelevant
		} else {
			out.addExpr(values[0].asWVal());
		}
		out.append(")");
		for (int i = 1; i < values.length; ++i) {
			out.append("[" + i + " := ");
			out.addExpr(values[i].asWVal()); // no brackets needed
			out.append("]");
		}
		out.append(", ");
		out.append(Integer.toString(values.length));
		out.append(")");
		return out;
	}

	private BoogieExpr createRecordConstructor(Expr.RecordInitialiser expr) {
		final BoogieExpr[] values = Arrays.stream(expr.getOperands().toArray(Expr.class)).map(this::boogieExpr)
				.toArray(BoogieExpr[]::new);
		final BoogieExpr out = new BoogieExpr(RECORD);
		Tuple<AbstractCompilationUnit.Identifier> fields = expr.getFields();
		// the values are presented in order according to the alphabetically sorted
		// field names!
		// FIXME: need to fix sorting of fields --- djp
		// Arrays.sort(fields);
		out.append("empty__record");
		for (int i = 0; i != values.length; ++i) {
			out.appendf("[%s := %s]", mangledWField(fields.get(i).get()), values[i].asWVal().toString());
		}
		out.setOp("[");
		return out;
	}

	/**
	 * Converts a Whiley field name into a Boogie field name. This translation is
	 * useful because in Boogie it is possible to have fields and variables with the
	 * same name, but our encoding in Boogie means they are all in the same name
	 * space (constants plus variables).
	 *
	 * @param field
	 * @return field prefixed with a dollar.
	 */
	private String mangledWField(String field) {
		return "$" + field;
	}

	/**
	 * Determines which functions/methods need renaming to resolve overloading.
	 *
	 * This should be called once at the beginning of each file/module. It
	 * initialises the global <code>functionOverloads</code> map.
	 *
	 * @param declarations
	 */
	private void resolveFunctionOverloading(Tuple<Decl> declarations) {
		// some common types
		// NOTE: the Any type was removed on 27 Oct 2017, so we simulate it by:  int|!int.
		// NOTE: negation types also removed on 9 Nov 2017, so we now hack 'any' as int|bool.
		//      (this is not at all equivalent, but here we use this 'any' type only as an approximate
		//       type for some predefined Boogie functions, to avoid name overloading issues.
		//       We do not rely on the semantics of those functions within this translator,
		//       so their types within the translator are not critical.)
		final Type type_Any = new Type.Union(Type.Int, Type.Bool, Type.Null);
		final Type[] any1 = { type_Any };
		final Type[] bool1 = { Type.Bool };
		final Type[] int1 = { Type.Int };
		final Type[] array1 = { new Type.Array(type_Any) };
		final Type[] ref1 = { new Type.Reference(type_Any) };
		final Type[] record1 = { new Type.Record(false, new Tuple<>()) };
		final Type[] object1 = { new Type.Record(true, new Tuple<>()) };
		// the following types are approximate - the params or returns are more specific
		// than needed.
		final Type.Function typePredicate = new Type.Function(new Tuple<>(bool1), new Tuple<>(any1));
		final Type.Function anyFunction = new Type.Function(new Tuple<>(any1), new Tuple<>(any1));
		final Type anyMethod = new Type.Method(new Tuple<>(new Type[0]), new Tuple<>(any1), new Tuple<>(),
				new Tuple<>());

		this.functionOverloads = new HashMap<>();

		// Now predefine all the functions in wval.bpl (as unmangled).
		// This is so that any user-defined functions with those names will be forced to
		// use mangled names!
		for (final String predef : new String[] { "isNull", "isInt", "isBool", "isArray", "isRecord", "isObject",
				"isRef", "isFunction", "isMethod", "isByte", }) {

			addPredefinedFunction(predef, typePredicate);
		}
		for (final String predef : new String[] { "toNull", "toInt", "toBool", "toArray", "toRecord", "toObject",
				"toRef", "toFunction", "toMethod", "toByte",
				// byte bitwise operators
				"byte_and", "byte_or", "byte_xor", "byte_shift_left", "byte_shift_right", "byte_invert",
				// int bitwise operators (unbounded)
				"bitwise_and", "bitwise_or", "bitwise_xor", "bitwise_shift_left", "bitwise_shift_right",
				"bitwise_invert",
				// higher-order apply operators
				"applyTo1", "applyTo2", "applyTo3" }) {
			addPredefinedFunction(predef, anyFunction);
		}
		addPredefinedFunction("fromInt", new Type.Function(new Tuple<>(any1), new Tuple<>(int1)));
		addPredefinedFunction("fromBool", new Type.Function(new Tuple<>(any1), new Tuple<>(bool1)));
		addPredefinedFunction("fromArray", new Type.Function(new Tuple<>(any1), new Tuple<>(array1)));
		addPredefinedFunction("fromRecord", new Type.Function(new Tuple<>(any1), new Tuple<>(record1)));
		addPredefinedFunction("fromObject", new Type.Function(new Tuple<>(any1), new Tuple<>(object1)));
		addPredefinedFunction("fromRef", new Type.Function(new Tuple<>(any1), new Tuple<>(ref1)));
		addPredefinedFunction("fromFunction", new Type.Function(new Tuple<>(any1), new Tuple<>(anyFunction)));
		addPredefinedFunction("fromMethod", new Type.Function(new Tuple<>(any1), new Tuple<>(anyMethod)));

		// first we look for exported/native functions, and mark them as NOT overloaded.
		for (final Decl d : declarations) {
			if (d instanceof Decl.Callable) {
				Decl.Callable m = (Decl.Callable) d;
				final boolean isExported = m.match(Modifier.Export.class) != null;
				final boolean isNative = m.match(Modifier.Native.class) != null;
				if (isExported || isNative) {
					addFunctionOverload(m.getName().get(), m.getType(), isExported, isNative);
				}
			}
		}
		// secondly, do the remaining function definitions
		for (final Decl d : declarations) {
			if (d instanceof Decl.Callable) {
				Decl.Callable m = (Decl.Callable) d;
				final boolean isExported = m.match(Modifier.Export.class) != null;
				final boolean isNative = m.match(Modifier.Native.class) != null;
				if (!isExported && !isNative) {
					addFunctionOverload(m.getName().get(), m.getType(), false, false);
				}
			}
		}
	}

	private void addFunctionOverload(final String name, final Type.Callable type, final boolean isExported,
			final boolean isNative) {
		Map<Type.Callable, String> map = this.functionOverloads.get(name);
		if (map == null) {
			// first one with this name needs no mangling!
			map = new HashMap<>();
			map.put(type, name);
			this.functionOverloads.put(name, map);
		} else if (isExported || isNative) {
			throw new IllegalArgumentException("Cannot overload exported function: " + name);
		} else if (!map.containsKey(type)) {
			final String mangled = name + "$" + (map.size() + 1);
			map.put(type, mangled);
			System.err.printf("mangle %s : %s to %s\n", name, type.toString(), mangled);
		}
	}

	private void addPredefinedFunction(String predef, Type.Function type) {
		final Map<Type.Callable, String> map = new HashMap<>();
		// System.err.printf("ADDING %s : %s as predefined.\n", predef, type);
		map.put(type, predef); // no name mangling, because this is a predefined function.
		this.functionOverloads.put(predef, map);
	}

	/**
	 * Mangles a function/method name, so that simple overloaded functions are
	 * possible.
	 *
	 * Note that we currently ignore module names here, as it is not obvious how to
	 * get the DeclID or the module of a function or method declaration. This may
	 * become an issue if we start verifying multi-module programs.
	 *
	 * @param name
	 *            the original name of the function or method.
	 * @param type
	 *            the type of the function or method.
	 * @return a human-readable name for the function/method.
	 */
	String mangledFunctionMethodName(String name, Type.Callable type) {
		final Map<Type.Callable, String> map = this.functionOverloads.get(name);
		if (map == null) {
			System.err.printf("Warning: function/method %s : %s assumed to be external, so not mangled.\n", name, type);
			return name; // no mangling!
		}
		final String result = map.get(type);
		if (result == null) {
			System.err.printf("Warning: unknown overload of function/method %s : %s was not mangled.\n", name, type);
			return name; // no mangling!
		}
		return result;
	}

	/**
	 * Encodes a fully qualified name into an allowable Boogie name.
	 *
	 * For the moment this ignores package names.
	 *
	 * @param name
	 * @return starts with "func__" so these are in a separate namespace.
	 */
	private String mangleFuncName(QualifiedName name) {
		return CONST_FUNC + name.getName().toString();
	}

	/**
	 * Recurses into the given type and makes sure all field names are declared.
	 *
	 * This should be called on all types, before each output definition.
	 *
	 * @param type
	 *            any kind of Whiley type.
	 * @param done
	 *            the names of the types that have already been processed. (This is
	 *            used to handle recursive and mutually-recursive types).
	 */
	@SuppressWarnings("StatementWithEmptyBody")
	private void declareFields(Type type, Set<Type> done) {
		if (done.contains(type)) {
			return; // this is a recursive type
		}
		done.add(type);
		if (type instanceof Type.Record) {
			final Type.Record t = (Type.Record) type;
			Tuple<Type.Field> fields = t.getFields();
			declareNewFields(fields);
			// now recurse into the types of those fields
			for (int i = 0; i != fields.size(); ++i) {
				declareFields(fields.get(i).getType(), done);
			}
		} else if (type instanceof Type.Array) {
			final Type.Array t = (Type.Array) type;
			declareFields(t.getElement(), done);
		} else if (type instanceof Type.Reference) {
			final Type.Reference t = (Type.Reference) type;
			declareFields(t.getElement(), done);
		} else if (type instanceof Type.Union) {
			final Type.Union t = (Type.Union) type;
			for (int i = 0; i != t.size(); ++i) {
				declareFields(t.get(i), done);
			}
		} else if (type instanceof Type.Callable) {
			final Type.Callable t = (Type.Callable) type;
			for (final Type b : t.getParameters()) {
				declareFields(b, done);
			}
			for (final Type b : t.getReturns()) {
				declareFields(b, done);
			}
		} else if (type instanceof Type.Nominal) {
			// A nominal type's definition RHS could contain fields.
			// But we have already processed that RHS when we reached the type definition.
		} else if (type instanceof Type.Primitive) {
			// no fields to declare
		} else {
			throw new IllegalArgumentException("unknown type encountered: " + type);
		}
	}

	private final AbstractVisitor recordVisitor = new AbstractVisitor() {
		@Override
		public void visitType(Type type) {
			declareFields(type, new HashSet<>());
		}

		@Override
		public void visitRecordInitialiser(Expr.RecordInitialiser expr) {
			for (AbstractCompilationUnit.Identifier f: expr.getFields()) {
				declareNewField(f.get());
			}
		}

		@Override
		public void visitRecordAccess(Expr.RecordAccess expr) {
			declareNewField(expr.getField().get());
		}

		@Override
		public void visitRecordUpdate(Expr.RecordUpdate expr) {
			declareNewField(expr.getField().get());
		}
	};

	/**
	 * A helper function that declares all new fields in a complete syntax tree.
	 *
	 * This should be called before that syntax tree is output.
	 *
	 * @param root
	 */
	private void declareFields(Stmt root) {
		recordVisitor.visitStatement(root);
	}

	private void declareFields(Tuple<Expr> roots) {
		for(Expr root : roots) {
			recordVisitor.visitExpression(root);
		}
	}

	private void declareLambdaFunction(Decl.Lambda decl) {
		// lambda function do not have useful names, so we generate a unique name and remember it.
		String lambdaName = CONST_FUNC + lambdaFunctionName.size();
		lambdaFunctionName.put(decl, lambdaName);
		this.out.printf("const unique %s:WFuncName;\n", lambdaName);

		// add axiom apply_n(closure_m(lambdaName, captured...), args...) = decl.getBody();
		StringBuilder decls = new StringBuilder();
		StringBuilder captureNames = new StringBuilder();
		String declSep = "";
		for (Decl.Variable c: decl.getCapturedVariables()) {
			decls.append(declSep + c.getName().get() + ":WVal");
			captureNames.append(", " + c.getName().get());
			declSep = ", ";
		}
		StringBuilder paramNames = new StringBuilder();
		for (Decl.Variable p: decl.getParameters()) {
			decls.append(declSep + p.getName().get() + ":WVal");
			paramNames.append(", " + p.getName().get());
			declSep = ", ";
		}
		// An example trigger of this axiom is: apply__2(closure__1(funcName,cap1),in1,in2).
		final String call = String.format("apply__%d(closure__%d(%s%s)%s)",
				decl.getParameters().size(),
				decl.getCapturedVariables().size(),
				lambdaName,
				captureNames.toString(),
				paramNames.toString()
				);
		BoogieExpr body = boogieExpr(decl.getBody()).asWVal();
		if (decls.length() == 0) {
			this.out.printf("axiom %s == %s;\n\n",
					call,
					body.toString());
		} else {
			this.out.printf("axiom (forall %s :: {%s} %s == %s);\n\n",
					decls.toString(),
					call,
					call,
					body.toString());
		}
	}

	/** Walks recursively through a constant and declares any function constants. */
	private final AbstractVisitor funcConstantVisitor = new AbstractVisitor() {
		@Override
		public void visitLambdaAccess(Expr.LambdaAccess l) {
			declareHigherOrderFunction(l.getDeclaration().getQualifiedName(), l.getDeclaration().getType());
		}

		@Override
		public void visitLambda(Decl.Lambda decl) {
			declareLambdaFunction(decl);
		}
	};

	private void declareFuncConstants(Stmt root) {
		funcConstantVisitor.visitStatement(root);
	}

	private void declareFuncConstants(Tuple<Expr> roots) {
		for(Expr root : roots) {
			funcConstantVisitor.visitExpression(root);
		}
	}

	private void declareFuncConstants(Expr root) {
		funcConstantVisitor.visitExpression(root);
	}

	/**
	 * Generate a fresh name for use as a bound variable.
	 *
	 * @param base
	 *            a prefix for the name.
	 * @return
	 */
	private String generateFreshBoundVar(String base) {
		this.uniqueId++;
		return base + this.uniqueId;
	}
}
