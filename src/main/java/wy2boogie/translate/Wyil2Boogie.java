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

import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import wybs.lang.NameID;
import wyil.lang.*;
import wyil.lang.Type;
import wyil.lang.Bytecode.AliasDeclaration;
import wyil.lang.Bytecode.Case;
import wyil.lang.Bytecode.Expr;
import wyil.lang.Bytecode.Stmt;
import wyil.lang.Bytecode.Switch;
import wyil.lang.Bytecode.VariableAccess;
import wyil.lang.Bytecode.VariableDeclaration;
import wyil.lang.Constant;
import wyil.lang.SyntaxTree.Location;
import wyil.lang.WyilFile.*;

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
 * TODO: move ALL method calls out of expressions?  (5 tests do this!)
 *
 * TODO: mangle Whiley var names to avoid Boogie reserved words and keywords?
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
 *   <li>System.Console sys and sys.out.println(string)</li>
 *   <li>DONE: indirect invoke (12 tests)</li>
 *   <li>DONE: references, new (17 tests), and dereferencing (17 tests)</li>
 *   <li>DONE: switch (14 tests)</li>
 *   <li>(!) lambda functions (17 tests)</li>
 *   <li>functions/methods with multiple return values (5 tests)</li>
 *   <li>DONE: continue statements and named blocks (3 tests)</li>
 *   <li>DONE (separate byte and int ops): bitwise operators (13 tests)</li>
 *   <li>DONE: generate type axioms for constants (tell Boogie the result of Whiley's type inference).</li>
 * </ul>
 *
 * @author David J. Pearce
 * @author Mark Utting
 */
public final class Wyil2Boogie {
    /** Prefix for the function/method names namespace (the WFuncName Boogie type). */
    public static final String CONST_FUNC = "func__";

    public static final String HEAP = "w__heap";
    public static final String ALLOCATED = "w__alloc";
    public static final String NEW = "new";
    public static final String NEW_REF = "ref__";
    // max number of 'new' expressions in a single statement.
    // TODO: calculate this on the fly within each procedure?
    public static final int NEW_REF_MAX = 4;

    private static final String IMMUTABLE_INPUT = "__0";

    /** The conjunction operator for pre/post conditions. */
    private static final String AND_OUTER = " &&\n      ";

    /** This is appended to each function/method name, for the precondition of that function. */
    public static final String METHOD_PRE = "__pre";

    /** Where the Boogie output is written. */
    protected PrintWriter out;

    /**
     * If true, then the Whiley bytecodes are printed as comments.
     * Note: this must be set via the '-v' flag in the main method.
     */
    protected boolean verbose = false;

    /** Keeps track of which (non-mangled) WField names have already been declared. */
    private final Set<String> declaredFields = new HashSet<>();

    /** Keeps track of which (non-mangled) function/method names have had their address taken. */
    private final Set<NameID> referencedFunctions = new HashSet<>();

    /** Used to generate unique IDs for bound variables. */
    private int uniqueId = 0;

    /** Keeps track of the mangled names for every function and method. */
    private Map<String, Map<Type.FunctionOrMethod, String>> functionOverloads;

    /** Input parameters of the current function/method. */
    List<Location<?>> inDecls;

    /** Output parameters of the current function/method. */
    List<Location<?>> outDecls;

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
    private Location<?> outerMethodCall;

    /**
     * A stack of labels for the loops we are inside (innermost label last).
     *
     * These labels are prefixed by "CONTINUE__" at the start of the loop body,
     * and by "BREAK__" after the end of the whole loop statement.
     */
    Deque<String> loopLabels = new ArrayDeque<>();

    private final AssertionGenerator vcg;

    /** Used to generate unique labels for each switch statement. */
    private int switchCount;

    /** Records the values within all the 'new' expressions in the current statement. */
    private final List<String> newAllocations = new ArrayList<>();

    public Wyil2Boogie(PrintWriter writer) {
        this.out = writer;
        this.vcg = new AssertionGenerator(this);
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
    protected void declareNewFields(String[] fields) {
        for (final String f : fields) {
            if (!this.declaredFields.contains(f)) {
                this.out.println("const unique " + mangledWField(f) + ":WField;");
                this.declaredFields.add(f);
            }
        }
    }

    /**
     * Declare any function or method names whose address is taken.
     *
     * This is careful to only declare a function the first time its name is seen.
     * So it is safe to call it on every function and method constant.
     */
    protected void declareNewFunction(NameID name, Type.FunctionOrMethod type) {
        if (!this.referencedFunctions.contains(name)) {
            final String func_const = CONST_FUNC + name.name();
            this.out.printf("const unique %s:WFuncName;\n", func_const);
            // At the moment, we assume indirect-invoke is used rarely, so for ONE type of function in each program.
            // TODO: extend this to handle more than one type of indirect-invoke result (different applyTo operators?)
            if (type.returns().length != 1) {
                throw new NotImplementedYet("multi-valued constant functions", null);
            }
            final Type ret = type.returns()[0];
            final Type[] args = type.params();
            final StringBuilder vDecl = new StringBuilder();
            final StringBuilder vCall = new StringBuilder();
            for (int i = 1; i <= args.length; i++) {
                if (i > 1) {
                    vDecl.append(", ");
                    vCall.append(", ");
                }
                vDecl.append("v" + i + ":WVal");
                vCall.append("v" + i);
            }
            final String call = String.format("applyTo%d(toFunction(f), %s)", args.length, vCall.toString());
            System.err.println("WARNING: assuming that all indirect function calls of arity " + args.length +
                    " return type " + ret);
            this.out.printf("axiom (forall f:WVal, %s :: isFunction(f) ==> ", vDecl.toString());
            this.out.print(typePredicate(call, ret));
            this.out.printf(");\n");
            this.out.printf("axiom (forall %s :: applyTo%d(%s, %s) == %s(%s));\n\n",
                    vDecl.toString(), args.length,
                    func_const, vCall.toString(),
                    name.name(), vCall.toString());
            this.referencedFunctions.add(name);
        }
    }

    // ======================================================================
    // Apply Method
    // ======================================================================

    public void apply(WyilFile module) throws IOException {
        resolveFunctionOverloading(module.functionOrMethods());
        this.out.printf("var %s:[WRef]WVal;\n", HEAP);
        this.out.printf("var %s:[WRef]bool;\n", ALLOCATED);
        // TODO: find a nicer way of making these local?
        for (int i = 0; i < NEW_REF_MAX; i++) {
            this.out.printf("var %s%d : WRef;\n", NEW_REF, i);
        }
        this.out.println();
        for(final WyilFile.Constant cd : module.constants()) {
            writeConstant(cd);
        }
        if(!module.constants().isEmpty()) {
            this.out.println();
        }
        for (final WyilFile.Type td : module.types()) {
            writeTypeSynonym(td);
            this.out.println();
            this.out.flush();
        }
        for(final FunctionOrMethod md : module.functionOrMethods()) {
            writeProcedure(md);
            this.out.println();
            this.out.flush();
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
    private void writeTypeSynonym(WyilFile.Type td) {
        if(this.verbose) {
            writeLocationsAsComments(td.getTree());
        }
        final Type t = td.type();
        declareFields(t, new HashSet<Type>());
        declareFields(td.getTree());
        declareFuncConstants(td.getTree());
        // writeModifiers(td.modifiers());
        final String param;
        if (!td.getTree().getLocations().isEmpty()) {
            @SuppressWarnings("unchecked")
			final
            Location<VariableDeclaration> loc = (Location<VariableDeclaration>) td.getTree().getLocation(0);
            param = loc.getBytecode().getName();
        } else {
            param = generateFreshBoundVar("r__");
        }
        this.out.print("function " + typePredicateName(td.name()) + "(" + param + ":WVal) returns (bool) {\n    ");
        this.out.print(typePredicate(param, t));
        if (!td.getInvariant().isEmpty()) {
            this.out.print(AND_OUTER);
            writeConjunction(td.getInvariant());
        }
        this.out.println(" }");
    }

    private void writeConstant(WyilFile.Constant cd) {
        if(this.verbose) {
            writeLocationsAsComments(cd.getTree());
        }
        declareFields(cd.constant().type(), new HashSet<Type>());
        declareFuncConstants(cd.constant());
        this.out.printf("const %s : WVal;\n", cd.name());
        this.out.printf("axiom %s == %s;\n", cd.name(), createConstant(cd.constant()).asWVal());
        final String typePred = typePredicate(cd.name(), cd.constant().type());
        this.out.printf("axiom %s;\n\n", typePred);
    }

    /**
     * Generates a Boogie procedure (and implementation) for the given Whiley function or method.
     *
     * We also generate a 'precondition function' called f__pre, which is true if the inputs
     * satisfy all the typing conditions and preconditions of the function or method.
     *
     * For a function f, we generate a Boogie function f, as well as a procedure f_impl.
     * The procedure is used to verify the code against pre/post.
     * This is because Boogie functions cannot include code,
     * they are uninterpreted functions or with an expression body only.
     *
     * The function encodes just the pre=>post properties,
     * and is callable from parts of the specification.
     *
     * @param method
     */
    private void writeProcedure(FunctionOrMethod method) {
        final Type.FunctionOrMethod ft = method.type();
        declareFields(method.getTree());
        declareFuncConstants(method.getTree());
        final String name = mangledFunctionMethodName(method.name(), method.type());
        final int inSize = ft.params().length;
        final int outSize = ft.returns().length;
        this.inDecls = method.getTree().getLocations().subList(0, inSize);
        this.outDecls = method.getTree().getLocations().subList(inSize, inSize + outSize);
        assert this.inDecls.size() == inSize;
        assert this.outDecls.size() == outSize;
        if (outSize > 1) {
            throw new NotImplementedYet("multiple return values:" + name, null);
        }
        // define a function for the precondition of this method.
        writeMethodPre(name + METHOD_PRE, method, method.getPrecondition());
        String procedureName = name;
        if (ft instanceof Type.Function) {
            writeFunction(name, method);
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
        // Part of the postcondition is the type and type constraints of each output variable.
        final Type[] outputs = method.type().returns();
        for (int i = 0; i != outputs.length; ++i) {
            final VariableDeclaration locn = (VariableDeclaration) this.outDecls.get(i).getBytecode();
            final String inName = locn.getName();
            this.out.printf("    ensures %s;\n", typePredicate(inName, outputs[i]));
        }
        for (final Location<Expr> postcondition : method.getPostcondition()) {
            this.out.printf("    ensures %s;\n", boogieBoolExpr(postcondition).toString());
        }
        if(this.verbose) {
            writeLocationsAsComments(method.getTree());
        }
        final Map<String, Type> mutatedInputs = findMutatedInputs(method);
        this.out.print("implementation ");
        writeSignature(procedureName, method, mutatedInputs);
        if (method.getBody() != null) {
            this.out.println();
            this.out.println("{");
            writeLocalVarDecls(method.getTree().getLocations());

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

    private Map<String, Type> findMutatedInputs(FunctionOrMethod method) {
        final Map<String, Type> result = new LinkedHashMap<>();
        final List<Location<?>> locations = method.getTree().getLocations();
        for (final Location<?> loc0 : locations) {
            if (loc0.getBytecode() instanceof Bytecode.Assign) {
                final Bytecode.Assign assign = (Bytecode.Assign) loc0.getBytecode();
                for (final int i : assign.leftHandSide()) {
                    Location<?> loc = locations.get(i);
                    int opcode = loc.getBytecode().getOpcode();
                    while (opcode == Bytecode.OPCODE_arrayindex
                            || opcode == Bytecode.OPCODE_fieldload
                            || opcode == Bytecode.OPCODE_varcopy
                            || opcode == Bytecode.OPCODE_varmove) {
                        loc = loc.getOperand(0);
                        opcode = loc.getBytecode().getOpcode();
                    }
                    // TODO: add this? loc = getVariableDeclaration(loc);
                    final int index = method.getTree().getIndexOf(loc);
                    if (index < this.inDecls.size()) {
                        // this is a mutated input!
                        @SuppressWarnings("unchecked")
						final
                        Location<VariableDeclaration> decl = (Location<VariableDeclaration>) loc;
                        final String name = decl.getBytecode().getName();
                        System.err.printf("MUTATED INPUT %s : %s\n", name, decl.getType());
                        result.put(name, decl.getType());
                    }
                }
            }
        }
        return result;
    }

    private void writeMethodPre(String name, FunctionOrMethod method, List<Location<Bytecode.Expr>> pre) {
        this.out.print("function ");
        this.out.print(name);
        this.out.print("(");
        writeParameters(method.type().params(), this.inDecls, null);
        this.out.print(") returns (bool)\n{\n      ");
        final Type[] parameters = method.type().params();
        for (int i = 0; i != parameters.length; ++i) {
            if (i != 0) {
                this.out.print(AND_OUTER);
            }
            final VariableDeclaration locn = (VariableDeclaration) this.inDecls.get(i).getBytecode();
            final String inName = locn.getName();
            this.out.print(typePredicate(inName, parameters[i]));
        }
        if (parameters.length > 0) {
            this.out.print(AND_OUTER);
        }
        writeConjunction(pre);
        this.out.println("\n}");
    }

    /**
     * Writes out a Boogie function declaration, plus a pre implies post axiom.
     *
     * @param name the mangled name of the function
     * @param method all other details of the function
     */
    private void writeFunction(String name, FunctionOrMethod method) {
        assert method.isFunction();
        this.out.print("function ");
        this.out.print(name);
        this.out.print("(");
        writeParameters(method.type().params(), this.inDecls, null);
        if (method.type().returns().length == 0) {
            this.out.println(");");
            throw new IllegalArgumentException("function with no return values: " + method);
        } else {
            this.out.print(") returns (");
            writeParameters(method.type().returns(), this.outDecls, null);
            this.out.println(");");

            // write axiom: (forall in,out :: f(in)==out && f_pre(in) ==> types(out) && post)
            final String inVars = getNames(this.inDecls);
            final String outVars = getNames(this.outDecls);
            this.out.print("axiom (forall ");
            writeParameters(method.type().params(), this.inDecls, null);
            if (this.inDecls.size() > 0 && this.outDecls.size() > 0) {
                this.out.print(", ");
            }
            writeParameters(method.type().returns(), this.outDecls, null);
            this.out.print(" ::\n    ");
            // construct f(in)==out && f__pre(in)
            final String call = String.format("%s(%s) == (%s) && %s(%s)", name, inVars, outVars,
                    name + METHOD_PRE, getNames(this.inDecls));
            this.out.println(call);
            this.out.print("    ==>\n      ");
            // Now write the type and type constraints of each output variable.
            final Type[] outputs = method.type().returns();
            for (int i = 0; i != outputs.length; ++i) {
                if (i != 0) {
                    this.out.print(AND_OUTER);
                }
                final VariableDeclaration locn = (VariableDeclaration) this.outDecls.get(i).getBytecode();
                final String inName = locn.getName();
                this.out.print(typePredicate(inName, outputs[i]));
            }
            if (outputs.length > 0) {
                this.out.print(AND_OUTER);
            }
            writeConjunction(method.getPostcondition());
            this.out.println(");");
        }
        this.out.println();
    }

    /**
     * Get the names being declared.
     *
     * @param decls a list of declarations.
     * @return a comma-separated string of just the names being declared.
     */
    private String getNames(List<Location<?>> decls) {
        final StringBuilder result = new StringBuilder();
        for (int i = 0; i != decls.size(); ++i) {
            if (i != 0) {
                result.append(", ");
            }
            final VariableDeclaration locn = (VariableDeclaration) decls.get(i).getBytecode();
            result.append(locn.getName());
        }
        return result.toString();
    }

    /**
     * Writes a conjunction, and leaves it as a Boogie boolean value.
     *
     * @param preds
     */
    private void writeConjunction(List<Location<Bytecode.Expr>> preds) {
        if (preds.isEmpty()) {
            this.out.print("true");
        } else {
            String sep = "";
            for (final Location<Expr> pred : preds) {
                this.out.print(sep);
                sep = AND_OUTER;
                final BoogieExpr expr = boogieBoolExpr(pred);
                this.out.print(expr.withBrackets(" && ").toString());
            }
        }
    }

    private void writeSignature(String name, FunctionOrMethod method, Map<String, Type> mutatedInputs) {
        this.out.print(name);
        this.out.print("(");
        writeParameters(method.type().params(), this.inDecls, mutatedInputs);
        if (method.type().returns().length > 0) {
            this.out.print(") returns (");
            writeParameters(method.type().returns(), this.outDecls, null);
        }
        this.out.print(")");
    }

    /**
     * Writes just the declarations and type constraints of local variables of a function/method.
     *
     * This is done only at the top level of each procedure.
     * Boogie requires all local variables to be declared at the start
     * of each function/procedure.  So this writes out just one copy of each
     * variable declaration.  If a variable is declared more than once, with
     * different types, then we cannot easily translate this to Boogie, so we throw an exception.
     *
     * It is hard to distinguish local variable declarations from bound variables inside quantifiers
     * if we just do a linear scan of the Whiley bytecodes, so this method does a recursive descent
     * through the code part of the function or method, looking for local variable declarations,
     * and ignoring expressions and quantifiers.
     *
     * @param locs
     */
    private void writeLocalVarDecls(List<Location<?>> locs) {
        // We start after the input and output parameters.
        this.switchCount = 0;
        final Map<String, Type> locals = new LinkedHashMap<>(); // preserve order, but remove duplicates
        writeLocalVarDeclsRecursive(locs, locs.size() - 1, locals);
        // reset to zero so that we generate same numbers as we generate code.
        this.switchCount = 0;
    }

    /**
     * Does a recursive descent through all the statements in a function/method, looking for local variables.
     *
     * @param locs all locations in this function/method
     * @param pc   the program counter of the block or statement to check for local variables
     * @param done a map of all the local variables found (and declared) so far.
     */
    @SuppressWarnings("unchecked")
    private void writeLocalVarDeclsRecursive(List<Location<?>> locs, int pc, Map<String, Type> done) {
        final Bytecode bytecode = locs.get(pc).getBytecode();
        if (bytecode instanceof VariableDeclaration) {
            final Location<VariableDeclaration> decl = (Location<VariableDeclaration>) locs.get(pc);
            final String name = decl.getBytecode().getName();
            final Type prevType = done.get(name);
            if (prevType == null) {
                done.put(name, decl.getType());
                tabIndent(1);
                this.out.printf("var %s : WVal where %s;\n", name, typePredicate(name, decl.getType()));
            } else if (!prevType.equals(decl.getType())) {
                throw new NotImplementedYet("local var " + name + " has multiple types", locs.get(pc));
            }
        } else if (bytecode instanceof Bytecode.Block) {
            // loop through all statements in this block
            final Bytecode.Block block = (Bytecode.Block) bytecode;
            for (final int b : block.getOperands()) {
                writeLocalVarDeclsRecursive(locs, b, done);
            }
        } else if (bytecode instanceof Stmt) {
            if (bytecode instanceof Switch) {
                this.switchCount++;
                tabIndent(1);
                // we don't bother recording these in the 'done' map, since each switch has a unique variable.
                this.out.printf("var %s : WVal;\n", createSwitchVar(this.switchCount));
            }
            // loop through all child blocks
            final Stmt code = (Stmt) bytecode;
            for (final int b : code.getBlocks()) {
                writeLocalVarDeclsRecursive(locs, b, done);
            }
        }
    }

    /** A unique name for each switch statement within a procedure. */
    private String createSwitchVar(int count) {
        return "switch" + count + "__value";
    }

    private void writeLocationsAsComments(SyntaxTree tree) {
        final List<Location<?>> locations = tree.getLocations();
        for(int i=0;i!=locations.size();++i) {
            final Location<?> loc = locations.get(i);
            final String id = String.format("%1$" + 3 + "s", "#" + i);
            final String type = String.format("%1$-" + 8 + "s", Arrays.toString(loc.getTypes()));
            this.out.println("// " + id + " " + type + " " + loc.getBytecode());
        }
    }

    private void writeParameters(Type[] parameters, List<Location<?>> decls, Map<String, Type> rename) {
        for (int i = 0; i != parameters.length; ++i) {
            if (i != 0) {
                this.out.print(", ");
            }
            final VariableDeclaration locn = (VariableDeclaration) decls.get(i).getBytecode();
            String name = locn.getName();
            if (rename != null && rename.containsKey(name)) {
                name = name + IMMUTABLE_INPUT;
            }
            this.out.print(name + ":WVal");
        }
    }

    private void writeBlock(int indent, Location<Bytecode.Block> block) {
        for (int i = 0; i != block.numberOfOperands(); ++i) {
            writeStatement(indent, block.getOperand(i));
        }
    }

    @SuppressWarnings("unchecked")
    private void writeStatement(int indent, Location<?> c) {
        tabIndent(indent+1);
        switch(c.getOpcode()) {
        case Bytecode.OPCODE_aliasdecl:
            writeAliasDeclaration(indent, (Location<Bytecode.AliasDeclaration>) c);
            break;
        case Bytecode.OPCODE_assert:
            this.vcg.checkPredicate(indent, c.getOperand(0));
            writeAssert(indent, (Location<Bytecode.Assert>) c); // should not contain 'new'
            break;
        case Bytecode.OPCODE_assume:
            this.vcg.checkPredicate(indent, c.getOperand(0));
            writeAssume(indent, (Location<Bytecode.Assume>) c); // should not contain 'new'
            break;
        case Bytecode.OPCODE_assign:
            final Location<?>[] lhs = c.getOperandGroup(SyntaxTree.LEFTHANDSIDE);
            final Location<?>[] rhs = c.getOperandGroup(SyntaxTree.RIGHTHANDSIDE);
            this.vcg.checkPredicates(indent, lhs);
            this.vcg.checkPredicates(indent, rhs);
            writeAssign(indent, (Location<Bytecode.Assign>) c);
            break;
        case Bytecode.OPCODE_break:
            writeBreak(indent, (Location<Bytecode.Break>) c);
            break;
        case Bytecode.OPCODE_continue:
            writeContinue(indent, (Location<Bytecode.Continue>) c);
            break;
        case Bytecode.OPCODE_debug:
            writeDebug(indent, (Location<Bytecode.Debug>) c);
            break;
        case Bytecode.OPCODE_dowhile:
            writeDoWhile(indent, (Location<Bytecode.DoWhile>) c);
            break;
        case Bytecode.OPCODE_fail:
            writeFail(indent, (Location<Bytecode.Fail>) c);
            break;
        case Bytecode.OPCODE_if:
        case Bytecode.OPCODE_ifelse:
            this.vcg.checkPredicate(indent, c.getOperand(0));
            writeIf(indent, (Location<Bytecode.If>) c);
            break;
        case Bytecode.OPCODE_indirectinvoke:
            // TODO: check arguments against the precondition?
            this.out.print("call "); // it should be a method, not a function
            this.outerMethodCall = c;
            writeIndirectInvoke(indent, (Location<Bytecode.IndirectInvoke>) c);
            this.outerMethodCall = null;
            break;
        case Bytecode.OPCODE_invoke:
            // TODO: check arguments against the precondition!
            this.out.print("call "); // it should be a method, not a function
            this.outerMethodCall = c;
            writeInvoke(indent, (Location<Bytecode.Invoke>) c);
            this.outerMethodCall = null;
            break;
        case Bytecode.OPCODE_namedblock:
            writeNamedBlock(indent, (Location<Bytecode.NamedBlock>) c);
            break;
        case Bytecode.OPCODE_while:
            this.vcg.checkPredicate(indent, c.getOperand(0));
            final Location<?>[] invars = c.getOperandGroup(0);
            this.vcg.checkPredicates(indent, invars);
            writeWhile(indent, (Location<Bytecode.While>) c);
            break;
        case Bytecode.OPCODE_return:
            this.vcg.checkPredicates(indent, c.getOperands());
            writeReturn(indent, (Location<Bytecode.Return>) c);
            break;
        case Bytecode.OPCODE_skip:
            writeSkip(indent, (Location<Bytecode.Skip>) c);
            break;
        case Bytecode.OPCODE_switch:
            this.vcg.checkPredicate(indent, c.getOperand(0));
            writeSwitch(indent, (Location<Bytecode.Switch>) c);
            break;
        case Bytecode.OPCODE_vardeclinit:
            this.vcg.checkPredicate(indent, c.getOperand(0));
            // fall through into the non-init case.
        case Bytecode.OPCODE_vardecl:
            // TODO: check the init expression
            writeVariableInit(indent, (Location<Bytecode.VariableDeclaration>) c);
            break;
        default:
            throw new NotImplementedYet("unknown bytecode encountered", c);
        }
    }

    private void writeAliasDeclaration(int indent, Location<AliasDeclaration> loc) {
        this.out.print("alias ");
        this.out.print(loc.getType());
        this.out.print(" ");
        final Location<VariableDeclaration> aliased = getVariableDeclaration(loc);
        this.out.print(aliased.getBytecode().getName());
        this.out.println(";");
    }

    /**
     * Generates a Boogie assertion to check the given conjecture.
     *
     * This is a helper function for AssertionGenerator.
     *
     * @param indent
     * @param bndVars
     * @param assumps a list of predicates we can assume to prove the conjecture.
     * @param conj a Boolean Boogie expression.
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
            tabIndent(indent+2);
        }
        if (assumps.size() > 0) {
            this.out.print("==> ");
        }
        // finally, print the main assertion.
        this.out.print(conj.as(BOOL).withBrackets(" ==> ").toString());
        this.out.println(close);
        tabIndent(indent+1); // get ready for next statement.
    }

    private void writeAssert(int indent, Location<Bytecode.Assert> c) {
        this.out.printf("assert %s;\n", boogieBoolExpr(c.getOperand(0)).toString());
    }

    private void writeAssume(int indent, Location<Bytecode.Assume> c) {
        this.out.printf("assume %s;\n", boogieBoolExpr(c.getOperand(0)).toString());
    }

    /**
     * Generates code for an assignment statement.
     *
     * For assignments with complex LHS, like a[i], this always updates the whole structure.
     * For example:
     * <ol>
     *   <li>Instead of a[e] := rhs, we do a := a[e := rhs]; (see ListAssign_Valid_1.whiley)</li>
     *   <li>Instead of a.field := rhs, we do a := a[$field := rhs]; (see RecordAssign_Valid_1.whiley)</li>
     *   <li>Instead of a[e].field := rhs, we do a := a[e := a[e][field := rhs]]; (see Subtype_Valid_3.whiley)</li>
     *   <li>Instead of a.field[e] := rhs, we do a := a[$field := a[$field][e := rhs]]; (see Complex_Valid_5.whiley)</li>
     *   <li>And so on, recursively, for deeper nested LHS.</li>
     *   <li>Instead of &a := rhs, we do heap := heap[a := rhs]; (see Reference_Valid_1.whiley)</li>
     * <ol>
     * In addition to the above, we have to add type conversions from WVal to array or record types, and back again.
     *
     * Calls the helper function <code>build_rhs()</code> to generate the complex RHS expressions.
     *
     * @param indent
     * @param stmt
     */
    private void writeAssign(int indent, Location<Bytecode.Assign> stmt) {
        final Location<?>[] lhs = stmt.getOperandGroup(SyntaxTree.LEFTHANDSIDE);
        final Location<?>[] rhs = stmt.getOperandGroup(SyntaxTree.RIGHTHANDSIDE);
        if (isMethod(rhs[0])) {
            this.outerMethodCall = rhs[0];
        }
        // first break down complex lhs terms, like a[i].f (into a base var and some indexes)
        final String[] lhsVars = new String[lhs.length];
        @SuppressWarnings("unchecked")
		final
        List<Index>[] lhsIndexes = new List[lhs.length];
        for (int i = 0; i != lhs.length; ++i) {
            lhsIndexes[i] = new ArrayList<>();
            lhsVars[i] = extractLhsBase(lhs[i], lhsIndexes[i]);
        }
        // then build up any complex rhs terms, like a[i := (a[i][$f := ...])]
        final String[] rhsExprs = new String[rhs.length];
        for (int i = 0; i != rhs.length; ++i) {
            if (i != 0) {
                this.out.print(", ");
            }
            final String newValue = writeAllocations(indent, rhs[i]).asWVal().toString();
            rhsExprs[i] = build_rhs(lhsVars[i], lhsIndexes[i], 0, newValue);
        }

        // now start printing the assignment
        if (isMethod(rhs[0])) {
            // Boogie distinguishes method & function calls!
            this.out.print("call ");
            this.outerMethodCall = null;
        }
        for (int i = 0; i != lhs.length; ++i) {
            if(i != 0) {
                this.out.print(", ");
            }
            this.out.print(lhsVars[i]);
        }
        if(lhs.length > 0) {
            final HashSet<String> noDups = new HashSet<String>(Arrays.asList(lhsVars));
            if (noDups.size() < lhs.length) {
                throw new NotImplementedYet("Conflicting LHS assignments not handled yet.", stmt);
            }
            this.out.print(" := ");
        }
        if (lhs.length != rhs.length) {
            if (Stream.of(lhsIndexes).anyMatch(x -> !x.isEmpty())) {
                throw new NotImplementedYet("Complex LHS vars in method call not handled yet.", stmt);
            }
            if (rhs.length != 1) {
                throw new NotImplementedYet("Assignment with non-matching LHS and RHS lengths.", stmt);
            }
        }
        for (int i = 0; i != rhs.length; ++i) {
            if (i != 0) {
                this.out.print(", ");
            }
            this.out.print(rhsExprs[i]);
        }
        this.out.println(";");
    }

    /**
     * Updates the heap and allocated flags for any 'new' side-effects in expr.
     * All expressions that could contain 'new' expressions should be processed via this method.
     * It returns the resulting Boogie expression just like expr(...), but first updates the heap etc.
     */
    private BoogieExpr writeAllocations(int indent, Location<?> expr) {
        this.newAllocations.clear();
        final BoogieExpr result = boogieExpr(expr);
        if (this.newAllocations.size() > 0) {
            String tab = "";  // first tab already done
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
    interface Index {
    }

    /** An index into an array. */
    class IntIndex implements Index {
        String index;

        public IntIndex(String i) {
            this.index = i;
        }

        @Override
        public String toString() {
            return "IntIndex(" + this.index + ")";
        }
    }

    /** An index into a given field within a record/object. */
    class FieldIndex implements Index {
        String field;
        public FieldIndex(String f) {
            this.field = f;
        }

        @Override
        public String toString() {
            return "FieldIndex(" + this.field + ")";
        }
    }

    /** An index into the heap (via a reference). */
    class DerefIndex implements Index {
        String ref;
        public DerefIndex(String ref) {
            this.ref = ref;
        }

        @Override
        public String toString() {
            return "DerefIndex(" + this.ref + ")";
        }
    }

    /**
     * Extracts base variable that is being assigned to.
     * Builds a list of all indexes into the 'indexes' list.
     *
     * TODO: wrap writeAllocations(indent, rhs[i]) around each expr(...)
     * in case the indexes contain 'new' expressions!
     *
     * @param loc the LHS expression AST.
     * @param indexes non-null list to append index bytecodes.
     * @return null if LHS is not an assignment to a (possibly indexed) variable.
     */
    private String extractLhsBase(Location<?> loc, List<Index> indexes) {
        if (loc.getBytecode().getOpcode() == Bytecode.OPCODE_arrayindex) {
            assert loc.getBytecode().numberOfOperands() == 2;
            final String indexStr = writeAllocations(0, loc.getOperand(1)).as(INT).toString();
            indexes.add(0, new IntIndex(indexStr));
            return extractLhsBase(loc.getOperand(0), indexes);
        } else if (loc.getBytecode().getOpcode() == Bytecode.OPCODE_fieldload) {
            assert loc.getBytecode().numberOfOperands() == 1;
            final String field = ((Bytecode.FieldLoad) (loc.getBytecode())).fieldName();
            indexes.add(0, new FieldIndex(field));
            return extractLhsBase(loc.getOperand(0), indexes);
        } else if (loc.getBytecode() instanceof Bytecode.Operator
                && loc.getBytecode().getOpcode() == Bytecode.OPCODE_dereference) {
            assert loc.getBytecode().numberOfOperands() == 1;
            final String ref = boogieExpr(loc.getOperand(0)).as(WREF).toString();
            indexes.add(0, new DerefIndex(ref));
            return HEAP;
        } else if (loc.getBytecode() instanceof Bytecode.VariableAccess) {
            final String base = boogieExpr(loc).asWVal().toString();
            return base;
        }
        throw new NotImplementedYet("complex assignment left-hand side", loc);
    }

    /**
     * Recursively builds a new RHS expression that updates one value inside a structure.
     *
     * @param wval_base is the Boogie string form of the structure that must be updated.
     * @param indexes is the array of all the indexes into the value that must be updated.
     * @param pos is which index (starting from 0) we are about to process.
     * @param newValue is the new value that must be assigned to the deepest part inside the structure.
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

    private boolean isMethod(Location<?> loc) {
        return (loc.getBytecode().getOpcode() == Bytecode.OPCODE_invoke
                && ((Bytecode.Invoke)loc.getBytecode()).type() instanceof Type.Method);
    }

    private void writeBreak(int indent, Location<Bytecode.Break> b) {
        this.out.printf("goto BREAK__%s;\n", this.loopLabels.getLast());
    }

    private void writeContinue(int indent, Location<Bytecode.Continue> b) {
        if (this.loopLabels.getLast().startsWith("SWITCH")) {
            // TODO: implement 'continue' within switch.
            throw new NotImplementedYet("continue inside switch", b);
        }
        this.out.printf("goto CONTINUE__%s;\n", this.loopLabels.getLast());
    }

    private void writeDebug(int indent, Location<Bytecode.Debug> b) {
        // out.println("debug;");
    }

    /**
     * Generate Boogie code for do-while.
     *
     * NOTE: Boogie does not have a do{S}while(C) where I command,
     * so we used to generate a while loop and use a boolean variable to force entry the first time.
     * This allows break/continue statements to work with the body S.
     * But this meant that the invariant was checked too soon (before whole loop).
     * <pre>
     *     do__while := true;
     *     while (do__while || C) invar I { S; do__while := false; }
     * </pre>
     * So now we translate directly to Boogie if and goto label statements:
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
    private void writeDoWhile(int indent, Location<Bytecode.DoWhile> b) {
        final Location<?>[] loopInvariant = b.getOperandGroup(0);
        // Location<?>[] modifiedOperands = b.getOperandGroup(1);
        this.loopLabels.addLast("DO__WHILE__" + this.loopLabels.size());
        this.out.printf("if (true) {\n");
        tabIndent(indent+2);
        this.out.printf("CONTINUE__%s:\n", this.loopLabels.getLast());
        writeBlock(indent+1, b.getBlock(0));
        tabIndent(indent+2);
        this.out.printf("// invariant:");
        this.vcg.checkPredicates(indent + 1, loopInvariant);
        writeLoopInvariant(indent + 2, "assert", loopInvariant);
        this.out.println();
        tabIndent(indent+2);
        this.vcg.checkPredicate(indent + 1, b.getOperand(0));
        this.out.printf("// while:\n");
        tabIndent(indent+2);
        final String cond = writeAllocations(indent, b.getOperand(0)).as(BOOL).toString();
        this.out.printf("if (%s) { goto CONTINUE__%s; }\n", cond, this.loopLabels.getLast());
        tabIndent(indent+1);
        this.out.println("}");
        tabIndent(indent+1);
        this.out.printf("BREAK__%s:\n", this.loopLabels.removeLast());
    }

    /**
     * Whiley fail means this point in the code should be unreachable.
     *
     * In the refinement calculus, and Boogie, 'assert false' forces the verifier to check this.
     *
     * @param indent
     * @param c
     */
    private void writeFail(int indent, Location<Bytecode.Fail> c) {
        this.out.println("assert false;");
    }

    private void writeIf(int indent, Location<Bytecode.If> b) {
        final String cond = writeAllocations(indent, b.getOperand(0)).as(BOOL).toString();
        this.out.printf("if (%s) {\n", cond);
        writeBlock(indent+1,b.getBlock(0));
        if (b.numberOfBlocks() > 1) {
            tabIndent(indent+1);
            this.out.println("} else {");
            writeBlock(indent+1,b.getBlock(1));
        }
        tabIndent(indent+1);
        this.out.println("}");
    }

    // TODO: decide how to encode indirect method calls
    private void writeIndirectInvoke(int indent, Location<Bytecode.IndirectInvoke> stmt) {
        final Location<?>[] operands = stmt.getOperands();
        final String[] args = new String[operands.length];
        args[0] = writeAllocations(indent, operands[0]).as(METHOD).toString();  // and/or as(FUNC)??
        for (int i = 1; i != operands.length; ++i) {
            args[i] = writeAllocations(indent, operands[i]).asWVal().toString();
        }
        writeCall(args);
    }

    private void writeInvoke(int indent, Location<Bytecode.Invoke> stmt) {
        final Location<?>[] operands = stmt.getOperands();
        final String[] args = new String[operands.length + 1];
        args[0] = mangledFunctionMethodName(stmt.getBytecode().name().name(), stmt.getBytecode().type());
        for (int i = 0; i != operands.length; ++i) {
            args[i + 1] = writeAllocations(indent, operands[i]).asWVal().toString();
        }
        writeCall(args);
    }

    private void writeCall(String[] args) {
        this.out.printf("%s(", args[0]);
        for (int i = 1; i != args.length; ++i) {
            if(i != 1) {
                this.out.print(", ");
            }
            this.out.print(args[i]);
        }
        this.out.println(");");
    }

    // TODO: named block
    private void writeNamedBlock(int indent, Location<Bytecode.NamedBlock> b) {
        this.out.print(b.getBytecode().getName());
        this.out.println(":");
        writeBlock(indent+1,b.getBlock(0));
        throw new NotImplementedYet("named block", b);
    }

    private void writeWhile(int indent, Location<Bytecode.While> b) {
        final Location<?>[] loopInvariant = b.getOperandGroup(0);
        // Location<?>[] modifiedOperands = b.getOperandGroup(1);
        final String cond = writeAllocations(indent, b.getOperand(0)).as(BOOL).toString();
        this.loopLabels.addLast("WHILE__" + this.loopLabels.size());
        this.out.printf("CONTINUE__%s:\n", this.loopLabels.getLast());
        tabIndent(indent+1);
        this.out.printf("while (%s)", cond);
        // out.print(" modifies ");
        // writeExpressions(modifiedOperands,out);
        writeLoopInvariant(indent + 2, "invariant", loopInvariant);
        this.out.println();
        tabIndent(indent + 1);
        this.out.println("{");
        writeBlock(indent+1,b.getBlock(0));
        tabIndent(indent+1);
        this.out.println("}");
        tabIndent(indent+1);
        this.out.printf("BREAK__%s:\n", this.loopLabels.removeLast());
    }

    private void writeLoopInvariant(int indent, String keyword, Location<?>[] loopInvariant) {
        if (loopInvariant.length > 0) {
            for (final Location<?> invariant : loopInvariant) {
                this.out.println();
                tabIndent(indent);
                this.out.printf("%s %s;", keyword, boogieBoolExpr(invariant).toString());
            }
        }
    }

    private void writeReturn(int indent, Location<Bytecode.Return> b) {
        // Boogie return does not take any expressions.
        // Instead, we must write to the result variables.
        final Location<?>[] operands = b.getOperands();
        final String[] args = new String[operands.length];
        if (operands.length == 1 && isMethod(operands[0])) {
            this.outerMethodCall = operands[0];
        }
        for (int i = 0; i != operands.length; ++i) {
            args[i] = writeAllocations(indent, operands[i]).asWVal().toString();
        }
        if (operands.length == 1 && isMethod(operands[0])) {
            this.out.print("call ");
            this.outerMethodCall = null;
        }
        for (int i = 0; i != operands.length; ++i) {
            final VariableDeclaration locn = (VariableDeclaration) this.outDecls.get(i).getBytecode();
            final String name = locn.getName();
            this.out.printf("%s := %s;\n", name, args[i]);
            tabIndent(indent+1);
        }
        this.out.println("return;");
    }

    private void writeSkip(int indent, Location<Bytecode.Skip> b) {
        // no output needed.  Boogie uses {...} blocks, so empty statements are okay.
    }

    /**
     * Implements switch as a non-deterministic goto to all the cases.
     *
     * Cases are numbered, so that 'continue' can jump to the next case.
     *
     * TODO: handle continue in switch.
     * (This just requires storing current case number i in a field,
     * so can goto "SWITCH(n)__CASE(i+1)".  But to support nested switches,
     * we will need a stack of these case numbers!).
     *
     * @param indent
     * @param sw
     */
    private void writeSwitch(int indent, Location<Bytecode.Switch> sw) {
        this.switchCount++;
        // we number each switch uniquely, so that nested switches and
        // non-nested switches in the same body all have distinct labels.
        this.loopLabels.addLast("SWITCH" + this.switchCount);
        final String var = createSwitchVar(this.switchCount);
        final Case[] cases = sw.getBytecode().cases();
        final String value = writeAllocations(indent, sw.getOperand(0)).asWVal().toString();
        this.out.printf("%s := %s;\n", var, value);
        // build all the case labels we could jump to.
        final StringBuilder labels = new StringBuilder();
        for (int i = 0; i < cases.length; i++) {
            if (i > 0) {
                labels.append(", ");
            }
            labels.append(this.loopLabels.getLast() + "__CASE" + i);
        }
        tabIndent(indent + 1);
        this.out.printf("goto %s;\n", labels.toString()); // non-deterministic
        final BoogieExpr defaultCond = new BoogieExpr(BoogieType.BOOL, "true");
        for (int i = 0; i < cases.length; i++) {
            writeCase(indent + 1, var, i, cases[i], sw.getBlock(i), defaultCond);
        }
        tabIndent(indent + 1);
        // We add a 'skip' statement after the BREAK label, just in case this switch is not inside a block.
        // For example, Switch_Valid_5.whiley.
        this.out.printf("BREAK__%s:\n", this.loopLabels.removeLast());
    }

    /**
     * Write one case (possibly with multiple values) and one block of code.
     * This could be the default case, which will have zero values.
     * @param indent
     * @param varStr the variable that contains the switch value
     * @param count the position (from zero) of the current case.
     * @param c the case matching values.
     * @param b the block of code.
     * @param defaultCond a Boogie term that is the negation of all matching conditions so far.
     */
    private void writeCase(int indent, String varStr, int count, Case c, Location<Bytecode.Block> b,
            BoogieExpr defaultCond) {
        // build the match condition:  var == val1 || var == val2 || ...
        final BoogieExpr var = new BoogieExpr(BoogieType.WVAL, varStr);
        BoogieExpr match = new BoogieExpr(BoogieType.BOOL);
        String op = null;
        for (final Constant cd : c.values()) {
            final BoogieExpr val = createConstant(cd).asWVal();
            final BoogieExpr test = new BoogieExpr(BoogieType.BOOL, var, " == ", val);
            final BoogieExpr negTest = new BoogieExpr(BoogieType.BOOL, var, " != ", val);
            defaultCond.addOp(" && ", negTest);
            if (op == null) {
                match = test;
            } else {
                op = " || ";
                match.addOp(op, test);
            }
        }
        tabIndent(indent + 1);
        this.out.printf(this.loopLabels.getLast() + "__CASE%d:\n",  count);
        tabIndent(indent + 2);
        final BoogieExpr assume = c.values().length == 0 ? defaultCond : match;
        this.out.printf("assume %s;\n", assume.as(BOOL).toString());
        writeBlock(indent + 1, b);
        tabIndent(indent + 2);
        this.out.printf("goto BREAK__%s;\n", this.loopLabels.getLast());
    }

    private void writeVariableInit(int indent, Location<VariableDeclaration> loc) {
        final Location<?>[] operands = loc.getOperands();
        if (operands.length > 0) {
            if (isMethod(operands[0])) {
                this.outerMethodCall = operands[0];
            }
            final BoogieExpr rhs = writeAllocations(indent, operands[0]).asWVal();
            if (isMethod(operands[0])) {
                this.out.printf("call ");
                this.outerMethodCall = null;
            }
            this.out.printf("%s := %s;\n", loc.getBytecode().getName(), rhs.toString());
        }
        // ELSE
        // TODO: Do we need a havoc here, to mimic non-det initialisation?
    }

    /** Convenience: equivalent to expr(_).as(BOOL). */
    protected BoogieExpr boogieBoolExpr(Location<?> expr) {
        return boogieExpr(expr).as(BOOL);
    }

    /** Convenience: equivalent to expr(_).as(INT). */
    protected BoogieExpr boogieIntExpr(Location<?> expr) {
        return boogieExpr(expr).as(INT);
    }

    @SuppressWarnings("unchecked")
    protected BoogieExpr boogieExpr(Location<?> expr) {
        switch (expr.getOpcode()) {
        case Bytecode.OPCODE_arraylength:
            return boogieArrayLength((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_arrayindex:
            return boogieArrayIndex((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_array:
            final BoogieExpr[] avals = Arrays.stream(expr.getOperands()).map(this::boogieExpr).toArray(BoogieExpr[]::new);
            return createArrayInitialiser(avals);

        case Bytecode.OPCODE_arraygen:
            return boogieArrayGenerator((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_convert:
            return boogieConvert((Location<Bytecode.Convert>) expr);

        case Bytecode.OPCODE_const:
            final Bytecode.Const c = (Bytecode.Const) expr.getBytecode();
            return createConstant(c.constant());

        case Bytecode.OPCODE_fieldload:
            return boogieFieldLoad((Location<Bytecode.FieldLoad>) expr);

        case Bytecode.OPCODE_indirectinvoke:
            return boogieIndirectInvokeExpr((Location<Bytecode.IndirectInvoke>) expr);

        case Bytecode.OPCODE_invoke:
            return boogieInvoke((Location<Bytecode.Invoke>) expr);

        case Bytecode.OPCODE_lambda:
            return boogieLambda((Location<Bytecode.Lambda>) expr);

        case Bytecode.OPCODE_record:
            final BoogieExpr[] rvals = Arrays.stream(expr.getOperands()).map(this::boogieExpr).toArray(BoogieExpr[]::new);
            return createRecordConstructor((Type.EffectiveRecord) expr.getType(), rvals);

        case Bytecode.OPCODE_newobject:
            return allocateNewObject((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_dereference:
            return boogieDereference((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_logicalnot:
            return boogiePrefixOp(BOOL, expr, "! ", BOOL);

        case Bytecode.OPCODE_neg:
            return boogiePrefixOp(INT, expr, "- ", INT);

        case Bytecode.OPCODE_all:
            return boogieQuantifier("forall", " ==> ", (Location<Bytecode.Quantifier>) expr);

        case Bytecode.OPCODE_some:
            return boogieQuantifier("exists", " && ", (Location<Bytecode.Quantifier>) expr);

        case Bytecode.OPCODE_add:
            return boogieInfixOp(INT, expr, " + ", INT);

        case Bytecode.OPCODE_sub:
            return boogieInfixOp(INT, expr, " - ", INT);

        case Bytecode.OPCODE_mul:
            return boogieInfixOp(INT, expr, " * ", INT);

        case Bytecode.OPCODE_div:
            // TODO: fix this for negative numbers.
            // Boogie 'mod' implements Euclidean division, whereas Whiley uses truncated division.
            // See https://en.wikipedia.org/wiki/Modulo_operation for explanations.
            // See http://boogie.codeplex.com/discussions/397357 for what Boogie does.
            return boogieInfixOp(INT, expr, " div ", INT);

        case Bytecode.OPCODE_rem:
            // TODO: fix this for negative numbers.
            // Boogie 'mod' implements Euclidean division, whereas Whiley uses truncated division.
            // See https://en.wikipedia.org/wiki/Modulo_operation for explanations.
            // See http://boogie.codeplex.com/discussions/397357 for what Boogie does.
            return boogieInfixOp(INT, expr, " mod ", INT);

        case Bytecode.OPCODE_bitwiseinvert:
            final String opType = getBitwiseType(expr.getOperand(0));
            final BoogieExpr lhs = boogieExpr(expr.getOperand(0)).as(INT);
            final String call = String.format("%s_invert(%s)", opType, lhs.toString());
            return new BoogieExpr(INT, call);

        case Bytecode.OPCODE_bitwiseor:
            return boogieBitwiseOp(expr, "or");
        case Bytecode.OPCODE_bitwisexor:
            return boogieBitwiseOp(expr, "xor");
        case Bytecode.OPCODE_bitwiseand:
            return boogieBitwiseOp(expr, "and");
        case Bytecode.OPCODE_shl:
            return boogieBitwiseOp(expr, "shift_left");
        case Bytecode.OPCODE_shr:
            return boogieBitwiseOp(expr, "shift_right");

        case Bytecode.OPCODE_eq:
            return boogieEquality((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_ne:
            final BoogieExpr eq = boogieEquality((Location<Bytecode.Operator>) expr);
            final BoogieExpr outNE = new BoogieExpr(BOOL);
            outNE.addOp("! ", eq);
            return outNE;

        case Bytecode.OPCODE_lt:
            return boogieInfixOp(INT, expr, " < ", BOOL);

        case Bytecode.OPCODE_le:
            return boogieInfixOp(INT, expr, " <= ", BOOL);

        case Bytecode.OPCODE_gt:
            return boogieInfixOp(INT, expr, " > ", BOOL);

        case Bytecode.OPCODE_ge:
            return boogieInfixOp(INT, expr, " >= ", BOOL);

        case Bytecode.OPCODE_logicaland:
            return boogieInfixOp(BOOL, expr, " && ", BOOL);

        case Bytecode.OPCODE_logicalor:
            return boogieInfixOp(BOOL, expr, " || ", BOOL);

        case Bytecode.OPCODE_is:
            return boogieIs((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_varcopy: // WAS: Bytecode.OPCODE_varaccess:
        case Bytecode.OPCODE_varmove: // WAS: Bytecode.OPCODE_varaccess:
            return boogieVariableAccess((Location<VariableAccess>) expr);

        default:
            throw new IllegalArgumentException("unknown bytecode encountered: " + expr.getBytecode());
        }
    }

    private BoogieExpr boogiePrefixOp(BoogieType argType, Location<?> c, String op, BoogieType resultType) {
        final BoogieExpr out = new BoogieExpr(resultType);
        final BoogieExpr rhs = boogieExpr(c.getOperand(0)).as(argType);
        out.addOp(op, rhs);
        return out;
    }

    private BoogieExpr boogieInfixOp(BoogieType argType, Location<?> c, String op, BoogieType resultType) {
        final BoogieExpr out = new BoogieExpr(resultType);
        final BoogieExpr lhs = boogieExpr(c.getOperand(0)).as(argType);
        final BoogieExpr rhs = boogieExpr(c.getOperand(1)).as(argType);
        out.addOp(lhs, op, rhs);
        return out;
    }

    private BoogieExpr boogieBitwiseOp(Location<?> c, String op) {
        final String opType = getBitwiseType(c.getOperand(0));
        final BoogieExpr lhs = boogieExpr(c.getOperand(0)).as(INT);
        final BoogieExpr rhs = boogieExpr(c.getOperand(1)).as(INT);
        final String call = String.format("%s_%s(%s, %s)", opType, op, lhs.toString(), rhs.toString());
        final BoogieExpr out = new BoogieExpr(INT, call);
        return out;
    }

    /** We distinguish bitwise operators on byte values from other int values. */
    private String getBitwiseType(Location<?> operand) {
        return operand.getType().equals(Type.T_BYTE) ? "byte" : "bitwise";
    }

    private BoogieExpr boogieVariableAccess(Location<VariableAccess> loc) {
        final Location<VariableDeclaration> vd = getVariableDeclaration(loc.getOperand(0));
        final String name = vd.getBytecode().getName();
        return new BoogieExpr(WVAL, name);
    }

    private BoogieExpr boogieArrayLength(Location<Bytecode.Operator> expr) {
        final BoogieExpr out = new BoogieExpr(INT);
        out.append("arraylen(");
        out.addExpr(boogieExpr(expr.getOperand(0)).asWVal());
        out.append(")");
        return out;
    }

    private BoogieExpr boogieArrayIndex(Location<Bytecode.Operator> expr) {
        final BoogieExpr out = new BoogieExpr(WVAL);
        out.addExpr(boogieExpr(expr.getOperand(0)).as(ARRAY));
        out.addOp("[", boogieIntExpr(expr.getOperand(1)));
        out.append("]");
        return out;
    }

    /**
     * Whiley array generators [val;len] are represented as:
     * <pre>
     * fromArray(arrayconst(val), len)
     * </pre>
     * @param expr
     */
    private BoogieExpr boogieArrayGenerator(Location<Bytecode.Operator> expr) {
        final BoogieExpr out = new BoogieExpr(WVAL);
        out.append("fromArray(arrayconst(");
        out.addExpr(boogieExpr(expr.getOperand(0)).asWVal());
        out.append("), ");
        out.addExpr(boogieExpr(expr.getOperand(1)).as(INT));
        out.append(")");
        return out;
    }

    private BoogieExpr boogieConvert(Location<Bytecode.Convert> expr) {
        // TODO: implement the record (and object?) conversion that drops fields?
        // See tests/valid/Coercion_Valid_9.whiley
        // TODO: are there any valid conversions in Boogie?
        // out.print("(" + expr.getType() + ") ");
        return boogieExpr(expr.getOperand(0));
    }

    private BoogieExpr boogieFieldLoad(Location<Bytecode.FieldLoad> expr) {
        final BoogieExpr out = new BoogieExpr(WVAL);
        out.addExpr(boogieExpr(expr.getOperand(0)).as(RECORD));
        out.appendf("[%s]", mangledWField(expr.getBytecode().fieldName()));
        return out;
    }

    private BoogieExpr boogieIndirectInvokeExpr(Location<Bytecode.IndirectInvoke> expr) {
        final Bytecode.IndirectInvoke invoke = expr.getBytecode();
        final int[] args = invoke.arguments();
        if (args.length != 1) {
            throw new NotImplementedYet("indirect invoke with " + args.length + " args", expr);
        }
        final BoogieExpr func = boogieExpr(expr.getOperand(0)).as(FUNCTION);
        final BoogieExpr arg = boogieExpr(expr.getOperandGroup(0)[0]).asWVal();
        // TODO: decide what to do if func is a method?
        final BoogieExpr out = new BoogieExpr(WVAL, "applyTo1(" + func + ", " + arg + ")");
        return out;
    }

    private BoogieExpr boogieInvoke(Location<Bytecode.Invoke> expr) {
        // TODO: check that it is safe to use unqualified DeclID names?
        final BoogieExpr out = new BoogieExpr(WVAL);
        final String name = expr.getBytecode().name().name();
        final Type.FunctionOrMethod type = expr.getBytecode().type();
        if (type instanceof Type.Method) {
            if (expr != this.outerMethodCall) {
                // The Whiley language spec 0.3.38, Section 3.5.5, says that because they are impure,
                // methods cannot be called inside specifications.
                throw new NotImplementedYet("call to method (" + name + ") from inside an expression", expr);
            }
        }
        out.append(mangledFunctionMethodName(name, type) + "(");
        final Location<?>[] operands = expr.getOperands();
        for(int i=0;i!=operands.length;++i) {
            if(i!=0) {
                out.append(", ");
            }
            out.addExpr(boogieExpr(operands[i]).asWVal());
        }
        out.append(")");
        return out;
    }

    // TODO: lambda
    // Question: some lambda expressions capture surrounding variables - how can we represent this in Boogie?
    private BoogieExpr boogieLambda(Location<Bytecode.Lambda> expr) {
        throw new NotImplementedYet("lambda", expr);
        /*
         * This Whiley lambda:
         * function g() -> func:
         *     return &(int x -> x + 1)
    generates the following bytecodes:
    Q1: Can we pre-generate a global function for most lambdas?
    Q2: How do we determine start of lambda body?  Input decls?

        procedure g__impl() returns ($:WVal);
        requires g__pre();
        ensures is_func($);
    //  #0 [tests/valid/Lambda_Valid_1:func] decl $
    //  #1 [int]    decl x
    //  #2 [int]    read (%1)
    //  #3 [int]    const 1
    //  #4 [int]    add (%2, %3)
    //  #5 [function(int)->(int)] lambda (%4) function(int)->(int)
    //  #6 []       return (%5)
    //  #7 []       block (%6)
    implementation g__impl() returns ($:WVal)
    {
        $ := lambda TODO;
        return;
    }
    */
        // return new BoogieExpr(WVAL, "lambda TODO");
    }

    /**
     * Sets up a heap allocation and returns the result heap reference as an expression.
     *
     * @param expr
     * @return a freshly allocated heap reference.
     */
    private BoogieExpr allocateNewObject(Location<Bytecode.Operator> expr) {
        final BoogieExpr be = boogieExpr(expr.getOperand(0)).asWVal();
        final String ref = NEW_REF + this.newAllocations.size();
        // this allocation will be done just BEFORE this expression
        this.newAllocations.add(be.toString());
        return new BoogieExpr(WREF, ref);
    }

    private BoogieExpr boogieDereference(Location<Bytecode.Operator> expr) {
        final BoogieExpr be = boogieExpr(expr.getOperand(0)).as(WREF);
        // TODO: assume the type information of out.
        final BoogieExpr out = new BoogieExpr(WVAL, "w__heap[" + be.toString() + "]");
        return out;
    }

    private BoogieExpr boogieIs(Location<Bytecode.Operator> c) {
        final BoogieExpr out = new BoogieExpr(BOOL);
        final Location<?> lhs = c.getOperand(0);
        final Location<?> rhs = c.getOperand(1);
        if (lhs.getBytecode() instanceof Bytecode.VariableAccess
                && rhs.getBytecode() instanceof Bytecode.Const) {
            final Location<VariableDeclaration> vd = getVariableDeclaration(lhs.getOperand(0));
            final String name = vd.getBytecode().getName();
            final Bytecode.Const constType = (Bytecode.Const) rhs.getBytecode();
            final Constant.Type type = (Constant.Type) constType.constant();
            out.append(typePredicate(name, type.value()));
        } else {
            throw new NotImplementedYet("expr is type", c);
        }
        return out;
    }

    /**
     * Equality and inequality requires type-dependent expansion.
     *
     * @param resultType
     * @param argType
     * @param c
     */
    private BoogieExpr boogieEquality(Location<Bytecode.Operator> c) {
        final Location<?> left = c.getOperand(0);
        final Location<?> right = c.getOperand(1);
        final Type leftType = c.getOperand(0).getType();
        final Type rightType = c.getOperand(1).getType();
        Type eqType = Type.Intersection(leftType, rightType);
        if (!isUsableEqualityType(eqType)) {
            if (isUsableEqualityType(leftType)) {
                eqType = leftType;
            } else if (isUsableEqualityType(rightType)) {
                eqType = rightType;
            } else {
                throw new NotImplementedYet("comparison of void intersection type: " + leftType + " and " + rightType, c);
            }
        }
        final BoogieExpr eq = boogieTypedEquality(eqType, boogieExpr(left), boogieExpr(right)).as(BOOL);
        return eq;
    }

    /** True for the types that our equality code generator can handle. */
    private boolean isUsableEqualityType(Type type) {
    		final String str = type.toString();
        return str.equals("bool") // WAS type instanceof Type.Bool
            || str.equals("int")  // WAS type instanceof Type.Int
            || str.equals("byte") // WAS type instanceof Type.Byte
            || str.equals("null") // WAS type instanceof Type.Null
            || (type instanceof Type.Array && isUsableEqualityType(((Type.Array) type).element()))
            || type instanceof Type.Record;  // should check all the field types too?
    }

    /**
     * A recursive helper function for writeEquality.
     *
     * @param eqType both left and right must belong to this type for the equality to be true.
     * @param left the LHS expression
     * @param right the RHS expression
     */
    private BoogieExpr boogieTypedEquality(Type eqType, BoogieExpr left, BoogieExpr right) {
    		final String eqTypeStr = eqType.toString();
        final BoogieExpr out = new BoogieExpr(BOOL);
        if (eqTypeStr.equals("null")) {
            // This requires special handling, since we do not have toNull and fromNull functions.
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
            final String[] fields = recType.getFieldNames().clone();
            Arrays.sort(fields);
            if (fields.length == 0) {
                out.append("true");
            }
            for (int i = 0; i < fields.length; i++) {
                final String field = fields[i];
                final String deref = "[" + mangledWField(field) + "]";
                final BoogieExpr leftVal = new BoogieExpr(WVAL, leftRec + deref);
                final BoogieExpr rightVal = new BoogieExpr(WVAL, rightRec + deref);
                final BoogieExpr feq = boogieTypedEquality(recType.getField(field), leftVal, rightVal).as(BOOL);
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
            final Type elemType = arrayType.element();
            // we check the length and all the values:
            //    arraylen(left) == arraylen(right)
            //    && (forall i:int :: 0 <= i && i < arraylen(a) ==> left[i] == right[i])
            final String index = generateFreshBoundVar("idx");
            final String deref = "[" + index + "]";
            final BoogieExpr leftVal = new BoogieExpr(WVAL, leftArray + deref);
            final BoogieExpr rightVal = new BoogieExpr(WVAL, rightArray + deref);
            out.appendf("arraylen(%s) == arraylen(%s) && (forall %s:int :: 0 <= %s && %s < arraylen(%s)",
                    left.asWVal().toString(),
                    right.asWVal().toString(),
                    index, index, index,
                    left.asWVal().toString());
            out.addOp(" ==> ", boogieTypedEquality(elemType, leftVal, rightVal).as(BOOL));
            out.append(")");
            out.setOp(" && "); // && is outermost, since the ==> is bracketed.
        } else {
            throw new NotImplementedYet("comparison of values of type: " + eqType
                    + ".  " + left.toString() + " == " + right.toString(), null);
        }
        return out;
    }

    @SuppressWarnings("unchecked")
    private BoogieExpr boogieQuantifier(String quant, String predOp, Location<Bytecode.Quantifier> c) {
        final BoogieExpr decls = new BoogieExpr(BOOL);
        final BoogieExpr constraints = new BoogieExpr(BOOL);
        for (int i = 0; i != c.numberOfOperandGroups(); ++i) {
            final Location<?>[] range = c.getOperandGroup(i);
            if (i != 0) {
                decls.append(", ");
                constraints.append(" && ");
            }
            // declare the bound variable: v:WVal
            final Location<VariableDeclaration>  v = (Location<VariableDeclaration>) range[SyntaxTree.VARIABLE];
            final String name = v.getBytecode().getName();
            decls.appendf("%s:WVal", name);

            // and add the constraint: isInt(v) && start <= v && v <= end
            final BoogieExpr vExpr = new BoogieExpr(WVAL, name).as(INT);
            final BoogieExpr start = boogieIntExpr(range[SyntaxTree.START]);
            final BoogieExpr end = boogieIntExpr(range[SyntaxTree.END]);
            constraints.append("isInt(" + name + ")");
            constraints.addOp(" && ", new BoogieExpr(BOOL, start, " <= ", vExpr));
            constraints.addOp(" && ", new BoogieExpr(BOOL, vExpr, " < ", end));
        }
        final BoogieExpr out = new BoogieExpr(BOOL);
        out.appendf("(%s %s :: ", quant, decls.toString());
        out.addOp(constraints, predOp, boogieBoolExpr(c.getOperand(SyntaxTree.CONDITION)));
        out.append(")");
        return out;
    }

    /**
     * Writes the given indentation levels into the output.
     *
     * @param indent
     */
    protected void tabIndent(int indent) {
        indent = indent * 4;
        for(int i=0;i<indent;++i) {
            this.out.print(" ");
        }
    }

    /** Returns an indent of the requested number of 'tab' stops. */
    protected String createIndent(int indent) {
        return indent <= 0 ? "" : String.format("%" + (indent * 4) + "s", "");
    }

    @SuppressWarnings("unchecked")
    private Location<VariableDeclaration> getVariableDeclaration(Location<?> loc) {
        switch (loc.getOpcode()) {
        case Bytecode.OPCODE_vardecl:
        case Bytecode.OPCODE_vardeclinit:
            return (Location<VariableDeclaration>) loc;
        case Bytecode.OPCODE_aliasdecl:
            return getVariableDeclaration(loc.getOperand(0));
        }
        throw new IllegalArgumentException("invalid location provided: " + loc);
    }

    /**
     * Translate the WyIL type into the type in Boogie.
     *
     * @param var the name of the variable being typed. Example "a".
     * @param type the WyIL type
     * @return a Boogie boolean typing predicate, such as "isInt(a)".
     *    The outermost operator will have precedence of && or tighter.
     */
    public String typePredicate(String var, Type type) {
    		final String typeStr = type.toString();
        if (type instanceof Type.Nominal) {
            final String typeName = ((Type.Nominal) type).name().name();
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
            final Type elemType = t.element();
            final String bndVar = generateFreshBoundVar("i__");
            final String elem = "toArray(" + var + ")[" + bndVar + "]";
            return String.format("isArray(%s) && (forall %s:int :: 0 <= %s && %s < arraylen(%s) ==> %s)",
                    var, bndVar, bndVar, bndVar, var, typePredicate(elem, elemType));
        }
        //		if (type instanceof Type.Void) {
        //			// this should not happen?
        //		}
        if (type instanceof Type.Record) {
            final Type.Record t = (Type.Record) type;
            // WAS final Map<String, Type> fields = t.fields();
            final String[] fields = t.getFieldNames();
            // add constraints about the fields
            final String objrec;
            //if (t.isOpen()) {
            //	objrec = "Object(" + var + ")";
            //} else {
            objrec = "Record(" + var + ")";
            //}
            final StringBuilder result = new StringBuilder();
            result.append("is" + objrec);
            // WAS for (final Map.Entry<String, Type> field : fields.entrySet()) {
            for (final String fieldName : fields) {
                result.append(" && ");
                final String elem = "to" + objrec + "[" + mangledWField(fieldName) + "]";
                final Type elemType = t.getField(fieldName);
                result.append(typePredicate(elem, elemType));
            }
            return result.toString();
        }
        if (type instanceof Type.Union) {
            // we generate the disjunction of all the bounds
            final Type.Union u = (Type.Union) type;
            String result = "((";
            String sep = "";
            for (final Type element : u.bounds()) {
                result += sep + typePredicate(var, element);
                sep = ") || (";
            }
            return result + "))";
        }
        if (type instanceof Type.Negation) {
            // we negate the type test
            final Type.Negation t = (Type.Negation) type;
            return "!" + typePredicate(var, t.element());
        }
        if (type instanceof Type.Reference) {
            // TODO: add constraints about the type pointed to.
            // Type.Reference ref = (Type.Reference) type;
            // translateType(?, ref.element(), stores);
            return "isRef(" + var + ")";
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
     * Create a user-defined type predicate name, like "is_list", from a type name "list".
     *
     * Note: we add the underscore to avoid name clashes with some of the predefined
     * predicates, like isInt(_).
     *
     * @param typeName a non-empty string.
     * @return a non-null string.
     */
    private String typePredicateName(String typeName) {
        return "is_" + typeName;
    }

    /**
     * Given a constant of the given type, cast it into a WVal value.
     *
     * @param cd a Whiley constant, with a type.
     * @return an expression string with type WVal.
     */
    private BoogieExpr createConstant(Constant cd) {
        final Type type = cd.type();
        if (cd instanceof Constant.Integer) {
            return new BoogieExpr(INT, cd.toString());
        } else if (cd instanceof Constant.Bool) {
            return new BoogieExpr(BOOL, cd.toString());
        } else if (cd instanceof Constant.Byte) {
            final Constant.Byte b = (Constant.Byte) cd;
            final int val = Byte.toUnsignedInt(b.value());
            return new BoogieExpr(INT, Integer.toString(val));
        } else if (cd instanceof Constant.Array) {
            final Constant.Array aconst = (Constant.Array) cd;
            final BoogieExpr[] values = aconst.values().stream().map(this::createConstant).toArray(BoogieExpr[]::new);
            return createArrayInitialiser(values);
        } else if (cd instanceof Constant.Null) {
            return new BoogieExpr(WVAL, "null"); // already a WVal
        } else if (cd instanceof Constant.Record) {
            final Constant.Record rec = (Constant.Record) cd;
            final List<String> fields = new ArrayList<String>(rec.values().keySet());
            Collections.sort(fields); // sort fields alphabetically
            final BoogieExpr[] vals = fields.stream().map(f -> createConstant(rec.values().get(f))).toArray(BoogieExpr[]::new);
            return createRecordConstructor((Type.EffectiveRecord) cd.type(), vals);
        } else if (cd instanceof Constant.FunctionOrMethod) {
            final Constant.FunctionOrMethod fm = (Constant.FunctionOrMethod) cd;
            return new BoogieExpr(WVAL, "fromFunction(" + CONST_FUNC + fm.name().name() + ")");
        } else {
            throw new NotImplementedYet("createConstant(" + cd + "):" + type, null);
        }
    }

    /**
     * Whiley array literals [a,b,c] (and strings) are represented as:
     * <pre>
     *   fromArray(arrayconst(a)[1 := b][2 := c], 3)
     * </pre>
     *
     * @param values the expressions that initialise the array.
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

    private BoogieExpr createRecordConstructor(Type.EffectiveRecord type, BoogieExpr[] values) {
        final BoogieExpr out = new BoogieExpr(RECORD);
        final String[] fields = type.getFieldNames().clone();
        // the values are presented in order according to the alphabetically sorted field names!
        Arrays.sort(fields);
        out.append("empty__record");
        for(int i = 0; i != values.length; ++i) {
            out.appendf("[%s := %s]", mangledWField(fields[i]), values[i].asWVal().toString());
        }
        out.setOp("[");
        return out;
    }

    /**
     * Converts a Whiley field name into a Boogie field name.
     * This translation is useful because in Boogie it is possible to have
     * fields and variables with the same name, but our encoding in Boogie
     * means they are all in the same name space (constants plus variables).
     *
     * @param field
     * @return field prefixed with a dollar.
     */
    protected String mangledWField(String field) {
        return "$" + field;
    }

    /**
     * Determines which functions/methods need renaming to resolve overloading.
     *
     * This should be called once at the beginning of each file/module.
     * It initialises the global <code>functionOverloads</code> map.
     *
     * @param functionOrMethods
     */
    private void resolveFunctionOverloading(Collection<WyilFile.FunctionOrMethod> functionOrMethods) {
        // some common types
        final Type[] any1 = { Type.T_ANY };
        final Type[] bool1 = { Type.T_BOOL };
        final Type[] int1 = { Type.T_INT };
        final Type[] array1 = { Type.Array(Type.T_ANY) };
        final Type[] ref1 = { Type.Reference("*", Type.T_ANY) };
        final Type[] record1 = { Type.Record(false, Collections.emptyList()) };
        final Type[]object1 = { Type.Record(true, Collections.emptyList()) };
        // the following types are approximate - the params or returns are more specific than needed.
        final Type.Function typePredicate = (Type.Function) Type.Function(bool1, any1);
        final Type.Function anyFunction = (Type.Function) Type.Function(any1, any1);
        final Type anyMethod = Type.Method(new String[0], new String[0], new Type[0], any1);

        this.functionOverloads = new HashMap<>();

        // Now predefine all the functions in wval.bpl (as unmangled).
        // This is so that any user-defined functions with those names will be forced to use mangled names!
        for (final String predef : new String[] {
                "isNull", "isInt", "isBool", "isArray", "isRecord",
                "isObject", "isRef", "isFunction", "isMethod", "isByte",
                }) {

            addPredefinedFunction(predef, typePredicate);
        }
        for (final String predef : new String[] {
                "toNull", "toInt", "toBool", "toArray", "toRecord",
                "toObject", "toRef", "toFunction", "toMethod", "toByte",
                // byte bitwise operators
                "byte_and", "byte_or", "byte_xor", "byte_shift_left",
                "byte_shift_right", "byte_invert",
                // int bitwise operators (unbounded)
                "bitwise_and", "bitwise_or", "bitwise_xor",
                "bitwise_shift_left", "bitwise_shift_right", "bitwise_invert",
                // higher-order apply operators
                "applyTo1", "applyTo2", "applyTo3"
                }) {
            addPredefinedFunction(predef, anyFunction);
        }
        addPredefinedFunction("fromInt", (Type.Function) Type.Function(any1, int1));
        addPredefinedFunction("fromBool", (Type.Function) Type.Function(any1, bool1));
        addPredefinedFunction("fromArray", (Type.Function) Type.Function(any1, array1));
        addPredefinedFunction("fromRecord", (Type.Function) Type.Function(any1, record1));
        addPredefinedFunction("fromObject", (Type.Function) Type.Function(any1, object1));
        addPredefinedFunction("fromRef", (Type.Function) Type.Function(any1, ref1));
        addPredefinedFunction("fromFunction", (Type.Function) Type.Function(any1, new Type[] { anyFunction }));
        addPredefinedFunction("fromMethod", (Type.Function) Type.Function(any1, new Type[] { anyMethod }));

        for (final WyilFile.FunctionOrMethod m : functionOrMethods) {
            final String name = m.name();
            final boolean isExported = m.hasModifier(Modifier.EXPORT);
            final boolean isNative = m.hasModifier(Modifier.NATIVE);
            Map<Type.FunctionOrMethod, String> map = this.functionOverloads.get(name);
            if (map == null) {
                // first one with this name needs no mangling!
                map = new HashMap<>();
                map.put(m.type(), name);
                this.functionOverloads.put(name, map);
            } else if (isExported || isNative) {
                throw new IllegalArgumentException("Cannot overload exported function: " + name);
            } else if (!map.containsKey(m.type())) {
                final String mangled = name + "$" + (map.size() + 1);
                map.put(m.type(), mangled);
                System.err.printf("mangle %s : %s to %s\n", name, m.type().toString(), mangled);
            }
        }
    }

    private void addPredefinedFunction(String predef, wyil.lang.Type.Function type) {
        final Map<Type.FunctionOrMethod, String> map = new HashMap<>();
        // System.err.printf("ADDING %s : %s as predefined.\n", predef, type);
        map.put(type, predef); // no name mangling, because this is a predefined function.
        this.functionOverloads.put(predef, map);
    }

    /**
     * Mangles a function/method name, so that simple overloaded functions are possible.
     *
     * Note that we currently ignore module names here, as it is not obvious how to get the
     * DeclID or the module of a function or method declaration.  This may become an issue
     * if we start verifying multi-module programs.
     *
     * @param name the original name of the function or method.
     * @param type the type of the function or method.
     * @return a human-readable name for the function/method.
     */
    protected String mangledFunctionMethodName(String name, Type.FunctionOrMethod type) {
        final Map<Type.FunctionOrMethod, String> map = this.functionOverloads.get(name);
        if (map == null) {
            System.err.printf("Warning: function/method %s : %s assumed to be external, so not mangled.\n",
                    name, type);
            return name;  // no mangling!
        }
        final String result = map.get(type);
        if (result == null) {
            System.err.printf("Warning: unknown overload of function/method %s : %s was not mangled.\n",
                    name, type);
            return name;  // no mangling!
        }
        return result;
    }

    /**
     * Recurses into the given type and makes sure all field names are declared.
     *
     * This should be called on all types, before each output definition.
     *
     * @param type any kind of Whiley type.
     * @param done the names of the types that have already been processed.
     *       (This is used to handle recursive and mutually-recursive types).
     */
    private void declareFields(Type type, Set<Type> done) {
        if (done.contains(type)) {
            return;  // this is a recursive type
        }
        if (type instanceof Type.Record) {
            final Type.Record t = (Type.Record) type;
            declareNewFields(t.getFieldNames());
        } else if (type instanceof Type.Array) {
            final Type.Array t = (Type.Array) type;
            done.add(t);
            declareFields(t.element(), done);
        } else if (type instanceof Type.Reference) {
            final Type.Reference t = (Type.Reference) type;
            done.add(t);
            declareFields(t.element(), done);
        } else if (type instanceof Type.Negation) {
            final Type.Negation t = (Type.Negation) type;
            done.add(t);
            declareFields(t.element(), done);
        } else if (type instanceof Type.Union) {
            final Type.Union t = (Type.Union) type;
            done.add(t);
            for (final Type b : t.bounds()) {
                declareFields(b, done);
            }
        } else if (type instanceof Type.FunctionOrMethod) {
            final Type.FunctionOrMethod t = (Type.FunctionOrMethod) type;
            done.add(t);
            for (final Type b : t.params()) {
                declareFields(b, done);
            }
            for (final Type b : t.returns()) {
                declareFields(b, done);
            }
        } else if (type instanceof Type.Leaf) {
            // no fields to declare
        } else {
            throw new IllegalArgumentException("unknown type encountered: " + type);
        }
    }

    /**
     * A helper function that declares all new fields in a complete syntax tree.
     *
     * This should be called before that syntax tree is output.
     *
     * @param tree
     */
    private void declareFields(SyntaxTree tree) {
        for (final Location<?> loc : tree.getLocations()) {
            final Type[] types = loc.getTypes();
            for (final Type t : types) {
                declareFields(t, new HashSet<Type>());
            }
        }
    }

    /** Walks recursively through a constant and declares any function constants. */
    private void declareFuncConstants(Constant cd) {
        if (cd instanceof Constant.Array) {
            final Constant.Array aconst = (Constant.Array) cd;
            for (final Constant c : aconst.values()) {
                declareFuncConstants(c);
            }
        } else if (cd instanceof Constant.Record) {
            final Constant.Record rec = (Constant.Record) cd;
            for (final Constant c : rec.values().values()) {
                declareFuncConstants(c);
            }
        } else if (cd instanceof Constant.FunctionOrMethod) {
            final Constant.FunctionOrMethod fm = (Constant.FunctionOrMethod) cd;
            declareNewFunction(fm.name(), fm.type());
        }
    }

    /** Walks through bytecode and declares any function constants. */
    private void declareFuncConstants(SyntaxTree tree) {
        final List<Location<?>> locations = tree.getLocations();
        for (int i = 0; i != locations.size(); ++i) {
            final Location<?> loc = locations.get(i);
            if (loc.getBytecode().getOpcode() == Bytecode.OPCODE_const
              && ((Bytecode.Const) loc.getBytecode()).constant() instanceof Constant.FunctionOrMethod) {
                final Bytecode.Const con = (Bytecode.Const) loc.getBytecode();
                final Constant.FunctionOrMethod bc = (Constant.FunctionOrMethod) con.constant();
                declareNewFunction(bc.name(), bc.type());
            }
        }
    }

    /**
     * Generate a fresh name for use as a bound variable.
     *
     * @param base a prefix for the name.
     * @return
     */
    private String generateFreshBoundVar(String base) {
        this.uniqueId++;
        return base + this.uniqueId;
    }
}
