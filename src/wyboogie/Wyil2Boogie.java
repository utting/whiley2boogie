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

package wyboogie;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
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

import javax.xml.transform.stream.StreamSource;

import wybs.lang.Build;
import wybs.util.StdProject;
import wycc.lang.NameID;
import wycc.lang.SyntaxError;
import wycc.lang.SyntaxError.InternalFailure;
import wycc.util.Pair;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.util.DirectoryRoot;
import wyil.Main.Registry;
import wyil.io.WyilFileReader;
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
import wyil.util.interpreter.Interpreter;
import wyc.WycMain;
import wyc.util.WycBuildTask;
import static wyboogie.BoogieType.*;

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
 * TODO: move all method calls out of expressions?  (35 tests do this!)
 *
 * TODO: refactor the BoogieExpr writeXXX() methods to boogieXXX().
 *
 * TODO: mangle Whiley var names to avoid Boogie reserved words and keywords?
 *
 * TODO: generate f(x)==e axiom for each Whiley function that is just 'return e'?
 *       (Because current translation only generates e into the __impl code of the function,
 *       so the semantics of the function are not visible elsewhere in the program.
 *       But this is a bit ad-hoc - the semantics should really be given in the postcondition!)
 *
 * TODO: implement missing language features, such as:
 * <ul>
 *   <li>DONE: indirect invoke (12 tests)</li>
 *   <li>references, new (17 tests), and dereferencing (17 tests)</li>
 *   <li>switch (14 tests)</li>
 *   <li>functions/methods with multiple return values (4 tests)</li>
 *   <li>(!) lambda functions (12 tests)</li>
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

    /** Special boolean variable used to emulate do-while loops. */
    private static final Object DO_WHILE_VAR = "do__while";

    /** Where the Boogie output is written. */
    protected PrintWriter out;

    /**
     * If true, then the Whiley bytecodes are printed as comments.
     * Note: this must be set via the '-v' flag in the main method.
     */
    protected boolean verbose = false;

    /** Keeps track of which (non-mangled) WField names have already been declared. */
    private Set<String> declaredFields = new HashSet<>();

    /** Keeps track of which (non-mangled) function/method names have had their address taken. */
    private Set<NameID> referencedFunctions = new HashSet<>();

    /** Used to generate unique IDs for bound variables. */
    private int uniqueId = 0;

    /** Keeps track of the mangled names for every function and method. */
    private Map<String, Map<Type.FunctionOrMethod, String>> functionOverloads;

    /** Input parameters of the current function/method. */
    List<Location<?>> inDecls;

    /** Output parameters of the current function/method. */
    List<Location<?>> outDecls;

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
    private List<String> newAllocations = new ArrayList<>();

    public Wyil2Boogie(PrintWriter writer) {
        this.out = writer;
        vcg = new AssertionGenerator(this);
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
    protected void declareNewFields(Set<String> fields) {
        for (String f : fields) {
            if (!declaredFields.contains(f)) {
                out.println("const unique " + mangleWField(f) + ":WField;");
                declaredFields.add(f);
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
        if (!referencedFunctions.contains(name)) {
            String func_const = CONST_FUNC + name.name();
            out.printf("const unique %s:WFuncName;\n", func_const);
            // At the moment, we assume indirect-invoke is used rarely, so for ONE type of function in each program.
            // TODO: extend this to handle more than one type of indirect-invoke result (different applyTo operators?)
            if (type.returns().size() != 1) {
                throw new NotImplementedYet("multi-valued constant functions", null);
            }
            Type ret = type.returns().get(0);
            ArrayList<Type> args = type.params();
            StringBuilder vDecl = new StringBuilder();
            StringBuilder vCall = new StringBuilder();
            for (int i = 1; i <= args.size(); i++) {
                if (i > 1) {
                    vDecl.append(", ");
                    vCall.append(", ");
                }
                vDecl.append("v" + i + ":WVal");
                vCall.append("v" + i);
            }
            String call = String.format("applyTo%d(toFunction(f), %s)", args.size(), vCall.toString());
            System.err.println("WARNING: assuming that all indirect function calls of arity " + args.size() +
                    " return type " + ret);
            out.printf("axiom (forall f:WVal, %s :: isFunction(f) ==> ", vDecl.toString());
            out.print(typePredicate(call, ret));
            out.printf(");\n");
            out.printf("axiom (forall %s :: applyTo%d(%s, %s) == %s(%s));\n\n",
                    vDecl.toString(), args.size(),
                    func_const, vCall.toString(),
                    name.name(), vCall.toString());
            referencedFunctions.add(name);
        }
    }

    // ======================================================================
    // Apply Method
    // ======================================================================

    public void apply(WyilFile module) throws IOException {
        resolveFunctionOverloading(module.functionOrMethods());
        out.printf("var %s:[WRef]WVal;\n", HEAP);
        out.printf("var %s:[WRef]bool;\n", ALLOCATED);
        // TODO: find a nicer way of making these local?
        for (int i = 0; i < NEW_REF_MAX; i++) {
            out.printf("var %s%d : WRef;\n", NEW_REF, i);
        }
        out.println();
        for(WyilFile.Constant cd : module.constants()) {
            writeConstant(cd);
        }
        if(!module.constants().isEmpty()) {
            out.println();
        }
        for (WyilFile.Type td : module.types()) {
            writeTypeSynonym(td);
            out.println();
            out.flush();
        }
        for(FunctionOrMethod md : module.functionOrMethods()) {
            writeProcedure(md);
            out.println();
            out.flush();
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
        if(verbose) {
            writeLocationsAsComments(td.getTree());
        }
        Type t = td.type();
        declareFields(t, new HashSet<Type>());
        declareFields(td.getTree());
        declareFuncConstants(td.getTree());
        // writeModifiers(td.modifiers());
        final String param;
        if (!td.getTree().getLocations().isEmpty()) {
            @SuppressWarnings("unchecked")
            Location<VariableDeclaration> loc = (Location<VariableDeclaration>) td.getTree().getLocation(0);
            param = loc.getBytecode().getName();
        } else {
            param = generateFreshBoundVar("r__");
        }
        out.print("function " + typePredicateName(td.name()) + "(" + param + ":WVal) returns (bool) {\n    ");
        out.print(typePredicate(param, t));
        if (!td.getInvariant().isEmpty()) {
            out.print(AND_OUTER);
            writeConjunction(td.getInvariant());
        }
        out.println(" }");
    }

    private void writeConstant(WyilFile.Constant cd) {
        if(verbose) {
            writeLocationsAsComments(cd.getTree());
        }
        declareFields(cd.constant().type(), new HashSet<Type>());
        declareFuncConstants(cd.constant());
        out.printf("const %s : WVal;\n", cd.name());
        out.printf("axiom %s == %s;\n", cd.name(), createConstant(cd.constant()).asWVal());
        String typePred = typePredicate(cd.name(), cd.constant().type());
        out.printf("axiom %s;\n\n", typePred);
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
        Type.FunctionOrMethod ft = method.type();
        declareFields(method.getTree());
        declareFuncConstants(method.getTree());
        String name = mangleFunctionMethodName(method.name(), method.type());
        int inSize = ft.params().size();
        int outSize = ft.returns().size();
        inDecls = method.getTree().getLocations().subList(0, inSize);
        outDecls = method.getTree().getLocations().subList(inSize, inSize + outSize);
        assert inDecls.size() == inSize;
        assert outDecls.size() == outSize;
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
        out.print("procedure ");
        writeSignature(procedureName, method, null);
        out.println(";");
        out.printf("    modifies %s, %s;\n", HEAP, ALLOCATED);
        for (int i = 0; i < NEW_REF_MAX; i++) {
            out.printf("    modifies %s%d;\n", NEW_REF, i);
        }
        out.printf("    requires %s(%s);\n", name + METHOD_PRE, getNames(inDecls));
        // Part of the postcondition is the type and type constraints of each output variable.
        List<Type> outputs = method.type().returns();
        for (int i = 0; i != outputs.size(); ++i) {
            VariableDeclaration locn = (VariableDeclaration) outDecls.get(i).getBytecode();
            String inName = locn.getName();
            out.printf("    ensures %s;\n", typePredicate(inName, outputs.get(i)));
        }
        for (Location<Expr> postcondition : method.getPostcondition()) {
            out.printf("    ensures %s;\n", boolExpr(postcondition).toString());
        }
        if(verbose) {
            writeLocationsAsComments(method.getTree());
        }
        Map<String, Type> mutatedInputs = findMutatedInputs(method);
        out.print("implementation ");
        writeSignature(procedureName, method, mutatedInputs);
        if (method.getBody() != null) {
            out.println();
            out.println("{");
            writeLocalVarDecls(method.getTree().getLocations());
            if (containsDoWhile(method.getTree())) {
                tabIndent(1);
                out.printf("var %s : bool;\n", DO_WHILE_VAR);
            }

            // now create a local copy of each mutated input!
            for (String naughty : mutatedInputs.keySet()) {
                tabIndent(1);
                out.printf("var %s : WVal where ", naughty);
                out.print(typePredicate(naughty, mutatedInputs.get(naughty)));
                out.println(";");
            }
            // now assign the original inputs to the copies.
            for (String naughty : mutatedInputs.keySet()) {
                tabIndent(1);
                out.printf("%s := %s;\n", naughty, naughty + IMMUTABLE_INPUT);
            }
            writeBlock(0, method.getBody());
            out.println("}");
        }
        inDecls = null;
        outDecls = null;
    }

    private boolean containsDoWhile(SyntaxTree tree) {
        for (Location<?> loc : tree.getLocations()) {
            if (loc.getBytecode() instanceof Bytecode.DoWhile) {
                return true;
            }
        }
        return false;
    }

    private Map<String, Type> findMutatedInputs(FunctionOrMethod method) {
        Map<String, Type> result = new LinkedHashMap<>();
        List<Location<?>> locations = method.getTree().getLocations();
        for (Location<?> loc0 : locations) {
            if (loc0.getBytecode() instanceof Bytecode.Assign) {
                Bytecode.Assign assign = (Bytecode.Assign) loc0.getBytecode();
                for (int i : assign.leftHandSide()) {
                    Location<?> loc = locations.get(i);
                    int opcode = loc.getBytecode().getOpcode();
                    while (opcode == Bytecode.OPCODE_arrayindex
                            || opcode == Bytecode.OPCODE_fieldload
                            || opcode == Bytecode.OPCODE_varaccess) {
                        loc = loc.getOperand(0);
                        opcode = loc.getBytecode().getOpcode();
                    }
                    // TODO: add this? loc = getVariableDeclaration(loc);
                    int index = method.getTree().getIndexOf(loc);
                    if (index < inDecls.size()) {
                        // this is a mutated input!
                        @SuppressWarnings("unchecked")
                        Location<VariableDeclaration> decl = (Location<VariableDeclaration>) loc;
                        String name = decl.getBytecode().getName();
                        System.err.printf("MUTATED INPUT %s : %s\n", name, decl.getType());
                        result.put(name, decl.getType());
                    }
                }
            }
        }
        return result;
    }

    private void writeMethodPre(String name, FunctionOrMethod method, List<Location<Bytecode.Expr>> pre) {
        out.print("function ");
        out.print(name);
        out.print("(");
        writeParameters(method.type().params(), inDecls, null);
        out.print(") returns (bool)\n{\n      ");
        List<Type> parameters = method.type().params();
        for (int i = 0; i != parameters.size(); ++i) {
            if (i != 0) {
                out.print(AND_OUTER);
            }
            VariableDeclaration locn = (VariableDeclaration) inDecls.get(i).getBytecode();
            String inName = locn.getName();
            out.print(typePredicate(inName, parameters.get(i)));
        }
        if (parameters.size() > 0) {
            out.print(AND_OUTER);
        }
        writeConjunction(pre);
        out.println("\n}");
    }

    /**
     * Writes out a Boogie function declaration, plus a pre implies post axiom.
     *
     * @param name the mangled name of the function
     * @param method all other details of the function
     */
    private void writeFunction(String name, FunctionOrMethod method) {
        assert method.isFunction();
        out.print("function ");
        out.print(name);
        out.print("(");
        writeParameters(method.type().params(), inDecls, null);
        if (method.type().returns().isEmpty()) {
            out.println(");");
            throw new IllegalArgumentException("function with no return values: " + method);
        } else {
            out.print(") returns (");
            writeParameters(method.type().returns(), outDecls, null);
            out.println(");");

            // write axiom: (forall in,out :: f(in)==out && f_pre(in) ==> types(out) && post)
            String inVars = getNames(inDecls);
            String outVars = getNames(outDecls);
            out.print("axiom (forall ");
            writeParameters(method.type().params(), inDecls, null);
            if (inDecls.size() > 0 && outDecls.size() > 0) {
                out.print(", ");
            }
            writeParameters(method.type().returns(), outDecls, null);
            out.print(" ::\n    ");
            // construct f(in)==out && f__pre(in)
            String call = String.format("%s(%s) == (%s) && %s(%s)", name, inVars, outVars,
                    name + METHOD_PRE, getNames(inDecls));
            out.println(call);
            out.print("    ==>\n      ");
            // Now write the type and type constraints of each output variable.
            List<Type> outputs = method.type().returns();
            for (int i = 0; i != outputs.size(); ++i) {
                if (i != 0) {
                    out.print(AND_OUTER);
                }
                VariableDeclaration locn = (VariableDeclaration) outDecls.get(i).getBytecode();
                String inName = locn.getName();
                out.print(typePredicate(inName, outputs.get(i)));
            }
            if (outputs.size() > 0) {
                out.print(AND_OUTER);
            }
            writeConjunction(method.getPostcondition());
            out.println(");");
        }
        out.println();
    }

    /**
     * Get the names being declared.
     *
     * @param decls a list of declarations.
     * @return a comma-separated string of just the names being declared.
     */
    private String getNames(List<Location<?>> decls) {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i != decls.size(); ++i) {
            if (i != 0) {
                result.append(", ");
            }
            VariableDeclaration locn = (VariableDeclaration) decls.get(i).getBytecode();
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
            out.print("true");
        } else {
            String sep = "";
            for (Location<Expr> pred : preds) {
                out.print(sep);
                sep = AND_OUTER;
                BoogieExpr expr = boolExpr(pred);
                out.print(expr.withBrackets(" && ").toString());
            }
        }
    }

    private void writeSignature(String name, FunctionOrMethod method, Map<String, Type> mutatedInputs) {
        out.print(name);
        out.print("(");
        writeParameters(method.type().params(), inDecls, mutatedInputs);
        if (!method.type().returns().isEmpty()) {
            out.print(") returns (");
            writeParameters(method.type().returns(), outDecls, null);
        }
        out.print(")");
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
        switchCount = 0;
        Map<String, Type> locals = new LinkedHashMap<>(); // preserve order, but remove duplicates
        writeLocalVarDeclsRecursive(locs, locs.size() - 1, locals);
        // reset to zero so that we generate same numbers as we generate code.
        switchCount = 0;
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
        Bytecode bytecode = locs.get(pc).getBytecode();
        if (bytecode instanceof VariableDeclaration) {
            Location<VariableDeclaration> decl = (Location<VariableDeclaration>) locs.get(pc);
            String name = decl.getBytecode().getName();
            Type prevType = done.get(name);
            if (prevType == null) {
                done.put(name, decl.getType());
                tabIndent(1);
                out.printf("var %s : WVal where %s;\n", name, typePredicate(name, decl.getType()));
            } else if (!prevType.equals(decl.getType())) {
                throw new NotImplementedYet("local var " + name + " has multiple types", locs.get(pc));
            }
        } else if (bytecode instanceof Bytecode.Block) {
            // loop through all statements in this block
            Bytecode.Block block = (Bytecode.Block) bytecode;
            for (int b : block.getOperands()) {
                writeLocalVarDeclsRecursive(locs, b, done);
            }
        } else if (bytecode instanceof Stmt) {
            if (bytecode instanceof Switch) {
                switchCount++;
                tabIndent(1);
                // we don't bother recording these in the 'done' map, since each switch has a unique variable.
                out.printf("var %s : WVal;\n", createSwitchVar(switchCount));
            }
            // loop through all child blocks
            Stmt code = (Stmt) bytecode;
            for (int b : code.getBlocks()) {
                writeLocalVarDeclsRecursive(locs, b, done);
            }
        }
    }

    /** A unique name for each switch statement within a procedure. */
    private String createSwitchVar(int count) {
        return "switch" + count + "__value";
    }

    private void writeLocationsAsComments(SyntaxTree tree) {
        List<Location<?>> locations = tree.getLocations();
        for(int i=0;i!=locations.size();++i) {
            Location<?> loc = locations.get(i);
            String id = String.format("%1$" + 3 + "s", "#" + i);
            String type = String.format("%1$-" + 8 + "s", Arrays.toString(loc.getTypes()));
            out.println("// " + id + " " + type + " " + loc.getBytecode());
        }
    }

    private void writeParameters(List<Type> parameters, List<Location<?>> decls, Map<String, Type> rename) {
        for (int i = 0; i != parameters.size(); ++i) {
            if (i != 0) {
                out.print(", ");
            }
            VariableDeclaration locn = (VariableDeclaration) decls.get(i).getBytecode();
            String name = locn.getName();
            if (rename != null && rename.containsKey(name)) {
                name = name + IMMUTABLE_INPUT;
            }
            out.print(name + ":WVal");
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
            vcg.checkPredicate(indent, c.getOperand(0));
            writeAssert(indent, (Location<Bytecode.Assert>) c); // should not contain 'new'
            break;
        case Bytecode.OPCODE_assume:
            vcg.checkPredicate(indent, c.getOperand(0));
            writeAssume(indent, (Location<Bytecode.Assume>) c); // should not contain 'new'
            break;
        case Bytecode.OPCODE_assign:
            Location<?>[] lhs = c.getOperandGroup(SyntaxTree.LEFTHANDSIDE);
            Location<?>[] rhs = c.getOperandGroup(SyntaxTree.RIGHTHANDSIDE);
            vcg.checkPredicates(indent, lhs);
            vcg.checkPredicates(indent, rhs);
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
            vcg.checkPredicate(indent, c.getOperand(0));
            writeIf(indent, (Location<Bytecode.If>) c);
            break;
        case Bytecode.OPCODE_indirectinvoke:
            // TODO: check arguments against the precondition?
            out.print("call "); // it should be a method, not a function
            writeIndirectInvoke(indent, (Location<Bytecode.IndirectInvoke>) c);
            break;
        case Bytecode.OPCODE_invoke:
            // TODO: check arguments against the precondition!
            out.print("call "); // it should be a method, not a function
            writeInvoke(indent, (Location<Bytecode.Invoke>) c);
            break;
        case Bytecode.OPCODE_namedblock:
            writeNamedBlock(indent, (Location<Bytecode.NamedBlock>) c);
            break;
        case Bytecode.OPCODE_while:
            vcg.checkPredicate(indent, c.getOperand(0));
            Location<?>[] invars = c.getOperandGroup(0);
            vcg.checkPredicates(indent, invars);
            writeWhile(indent, (Location<Bytecode.While>) c);
            break;
        case Bytecode.OPCODE_return:
            vcg.checkPredicates(indent, c.getOperands());
            writeReturn(indent, (Location<Bytecode.Return>) c);
            break;
        case Bytecode.OPCODE_skip:
            writeSkip(indent, (Location<Bytecode.Skip>) c);
            break;
        case Bytecode.OPCODE_switch:
            vcg.checkPredicate(indent, c.getOperand(0));
            writeSwitch(indent, (Location<Bytecode.Switch>) c);
            break;
        case Bytecode.OPCODE_vardeclinit:
            vcg.checkPredicate(indent, c.getOperand(0));
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
        out.print("alias ");
        out.print(loc.getType());
        out.print(" ");
        Location<VariableDeclaration> aliased = getVariableDeclaration(loc);
        out.print(aliased.getBytecode().getName());
        out.println(";");
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
        out.print("assert ");
        if (!bndVars.isEmpty()) {
            out.print("(forall ");
            close = ");";
            for (int i = 0; i < bndVars.size(); i++) {
                if (i > 0) {
                    out.print(", ");
                }
                out.print(bndVars.get(i) + ":WVal");
            }
            out.print(" :: ");
        }
        for (int i = 0; i < assumps.size(); i++) {
            if (i > 0) {
                out.print("&& ");
            }
            out.println(assumps.get(i).as(BOOL).withBrackets(" && ").toString());
            tabIndent(indent+2);
        }
        if (assumps.size() > 0) {
            out.print("==> ");
        }
        // finally, print the main assertion.
        out.print(conj.as(BOOL).withBrackets(" ==> ").toString());
        out.println(close);
        tabIndent(indent+1); // get ready for next statement.
    }

    private void writeAssert(int indent, Location<Bytecode.Assert> c) {
        out.printf("assert %s;\n", boolExpr(c.getOperand(0)).toString());
    }

    private void writeAssume(int indent, Location<Bytecode.Assume> c) {
        out.printf("assume %s;\n", boolExpr(c.getOperand(0)).toString());
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
        Location<?>[] lhs = stmt.getOperandGroup(SyntaxTree.LEFTHANDSIDE);
        Location<?>[] rhs = stmt.getOperandGroup(SyntaxTree.RIGHTHANDSIDE);
        List<Index> indexes = new ArrayList<>();
        String base = extractLhsBase(lhs[0], indexes);
        // TODO: remove this first 'if' since it is subsumed by the general case.
        if (base != null && lhs.length == 1) {
            // we have a single assignment with a complex LHS
            String newValue = writeAllocations(indent, rhs[0]).asWVal().toString();
            final String result = build_rhs(base, indexes, 0, newValue);
            out.printf("%s := %s", base, result);
        } else {
            if (isMethod(rhs[0])) {
                // Boogie distinguishes method & function calls!
                out.print("call ");
            }
            String[] lhsVars = new String[lhs.length];
            @SuppressWarnings("unchecked")
            List<Index>[] lhsIndexes = new List[lhs.length];
            for (int i = 0; i != lhs.length; ++i) {
                lhsIndexes[i] = new ArrayList<>();
                lhsVars[i] = extractLhsBase(lhs[i], lhsIndexes[i]);
                if(i != 0) {
                    out.print(", ");
                }
                // Was: out.print(expr(lhs[i]).asWVal().toString());
                out.print(lhsVars[i]);
            }
            if(lhs.length > 0) {
                HashSet<String> noDups = new HashSet<String>(Arrays.asList(lhsVars));
                if (noDups.size() < lhs.length) {
                    throw new NotImplementedYet("Conflicting LHS assignments not handled yet.", stmt);
                }
                out.print(" := ");
            }
            if (lhs.length != rhs.length) {
                if (Stream.of(lhsIndexes).anyMatch(x -> !x.isEmpty())) {
                    throw new NotImplementedYet("Complex LHS vars in method call not handled yet.", stmt);
                }
            }
            for (int i = 0; i != rhs.length; ++i) {
                if (i != 0) {
                    out.print(", ");
                }
                String newValue = expr(rhs[0]).asWVal().toString();
                final String rhsExpr = build_rhs(base, indexes, 0, newValue);
                // Was: out.print(expr(rhs[i]).asWVal().toString());
                out.print(rhsExpr);
            }
        }
        out.println(";");
    }

    /**
     * Updates the heap and allocated flags for any 'new' side-effects in expr.
     * All expressions that could contain 'new' expressions should be processed via this method.
     * It returns the resulting Boogie expression just like expr(...), but first updates the heap etc.
     */
    private BoogieExpr writeAllocations(int indent, Location<?> expr) {
        newAllocations.clear();
        BoogieExpr result = expr(expr);
        if (newAllocations.size() > 0) {
            String tab = "";  // first tab already done
            for (int i = 0; i < newAllocations.size(); i++) {
                String ref = NEW_REF + i;
                out.printf("%s// allocate %s\n", tab, ref);
                tab = makeIndent(indent + 1);
                out.printf("%s%s := %s(%s);\n", tab, ref, NEW, ALLOCATED);
                out.printf("%s%s := %s[%s := true];\n", tab, ALLOCATED, ALLOCATED, ref);
                out.printf("%s%s := %s[%s := %s];\n\n", tab, HEAP, HEAP, ref, newAllocations.get(i));
            }
            out.printf(tab);
            newAllocations.clear();
        }
        return result;
    }

    /** Some kind of index into a data structure. */
    interface Index {
    }

    /** An index into an array. */
    class IntIndex implements Index {
        Location<?> index;

        public IntIndex(Location<?> i) {
            this.index = i;
        }

        @Override
        public String toString() {
            return "IntIndex(" + index + ")";
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
            return "FieldIndex(" + field + ")";
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
            return "DerefIndex(" + ref + ")";
        }
    }

    /**
     * Extracts base variable that is being assigned to.
     * Builds a list of all indexes into the 'indexes' list.
     * @param loc the LHS expression AST.
     * @param indexes non-null list to append index bytecodes.
     * @return null if LHS is not an assignment to a (possibly indexed) variable.
     */
    private String extractLhsBase(Location<?> loc, List<Index> indexes) {
        if (loc.getBytecode().getOpcode() == Bytecode.OPCODE_arrayindex) {
            assert loc.getBytecode().numberOfOperands() == 2;
            indexes.add(0, new IntIndex(loc.getOperand(1)));
            return extractLhsBase(loc.getOperand(0), indexes);
        } else if (loc.getBytecode().getOpcode() == Bytecode.OPCODE_fieldload) {
            assert loc.getBytecode().numberOfOperands() == 1;
            String field = ((Bytecode.FieldLoad) (loc.getBytecode())).fieldName();
            indexes.add(0, new FieldIndex(field));
            return extractLhsBase(loc.getOperand(0), indexes);
        } else if (loc.getBytecode() instanceof Bytecode.Operator
                && loc.getBytecode().getOpcode() == Bytecode.OPCODE_dereference) {
            assert loc.getBytecode().numberOfOperands() == 1;
            String ref = expr(loc.getOperand(0)).as(WREF).toString();
            indexes.add(0, new DerefIndex(ref));
            return HEAP;
        } else if (loc.getBytecode() instanceof Bytecode.VariableAccess) {
            String base = expr(loc).asWVal().toString();
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
            Location<?> index = ((IntIndex) indexes.get(pos)).index;
            // Instead of a[e] := rhs, we do a := a[e := rhs];
            String a = "toArray(" + wval_base + ")";
            String indexStr = intExpr(index).toString();
            String newWValBase = String.format("%s[%s]", a, indexStr);
            String recValue = build_rhs(newWValBase, indexes, pos + 1, newValue);
            result = String.format("fromArray(%s[%s := %s], arraylen(%s))", a, indexStr, recValue, wval_base);
        } else if (indexes.get(pos) instanceof FieldIndex) {
            // Instead of a.field := rhs, we do a := a[$field := rhs];
            String field = ((FieldIndex) indexes.get(pos)).field;
            String r = "toRecord(" + wval_base + ")";
            String newWValBase = String.format("%s[%s]", r, mangleWField(field));
            String recValue = build_rhs(newWValBase, indexes, pos + 1, newValue);
            result = String.format("fromRecord(%s[%s := %s])", r, mangleWField(field), recValue);
        } else {
            if (pos != 0 || !wval_base.equals(HEAP)) {
                throw new NotImplementedYet("multiple levels of dereference := " + newValue, null);
            }
            String ref = ((DerefIndex) indexes.get(pos)).ref;
            String newWValBase = String.format("%s[%s]", HEAP, ref);
            String recValue = build_rhs(newWValBase, indexes, pos + 1, newValue);
            result = String.format("%s[%s := %s]", HEAP, ref, recValue);
        }
        return result;
    }

    private boolean isMethod(Location<?> loc) {
        return (loc.getBytecode().getOpcode() == Bytecode.OPCODE_invoke
                && ((Bytecode.Invoke)loc.getBytecode()).type() instanceof Type.Method);
    }

    private void writeBreak(int indent, Location<Bytecode.Break> b) {
        out.printf("goto BREAK__%s;\n", loopLabels.getLast());
    }

    private void writeContinue(int indent, Location<Bytecode.Continue> b) {
        if (loopLabels.getLast().startsWith("SWITCH")) {
            // TODO: implement 'continue' within switch.
            throw new NotImplementedYet("continue inside switch", b);
        }
        out.printf("goto CONTINUE__%s;\n", loopLabels.getLast());
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
        Location<?>[] loopInvariant = b.getOperandGroup(0);
        // Location<?>[] modifiedOperands = b.getOperandGroup(1);
        loopLabels.addLast("DO__WHILE__" + loopLabels.size());
        out.printf("if (true) {\n");
        tabIndent(indent+2);
        out.printf("CONTINUE__%s:\n", loopLabels.getLast());
        writeBlock(indent+1, b.getBlock(0));
        tabIndent(indent+2);
        out.printf("// invariant:");
        vcg.checkPredicates(indent + 1, loopInvariant);
        writeLoopInvariant(indent + 2, "assert", loopInvariant);
        out.println();
        tabIndent(indent+2);
        vcg.checkPredicate(indent + 1, b.getOperand(0));
        out.printf("// while:\n");
        tabIndent(indent+2);
        String cond = writeAllocations(indent, b.getOperand(0)).as(BOOL).toString();
        out.printf("if (%s) { goto CONTINUE__%s; }\n", cond, loopLabels.getLast());
        tabIndent(indent+1);
        out.println("}");
        tabIndent(indent+1);
        out.printf("BREAK__%s:\n", loopLabels.removeLast());
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
        out.println("assert false;");
    }

    private void writeIf(int indent, Location<Bytecode.If> b) {
        String cond = writeAllocations(indent, b.getOperand(0)).as(BOOL).toString();
        out.printf("if (%s) {\n", cond);
        writeBlock(indent+1,b.getBlock(0));
        if (b.numberOfBlocks() > 1) {
            tabIndent(indent+1);
            out.println("} else {");
            writeBlock(indent+1,b.getBlock(1));
        }
        tabIndent(indent+1);
        out.println("}");
    }

    // TODO: decide how to encode indirect method calls
    private void writeIndirectInvoke(int indent, Location<Bytecode.IndirectInvoke> stmt) {
        Location<?>[] operands = stmt.getOperands();
        String[] args = new String[operands.length];
        args[0] = writeAllocations(indent, operands[0]).as(METHOD).toString();  // and/or as(FUNC)??
        for (int i = 1; i != operands.length; ++i) {
            args[i] = writeAllocations(indent, operands[i]).asWVal().toString();
        }
        writeCall(args);
    }

    private void writeInvoke(int indent, Location<Bytecode.Invoke> stmt) {
        Location<?>[] operands = stmt.getOperands();
        String[] args = new String[operands.length + 1];
        args[0] = mangleFunctionMethodName(stmt.getBytecode().name().name(), stmt.getBytecode().type());
        for (int i = 0; i != operands.length; ++i) {
            args[i + 1] = writeAllocations(indent, operands[i]).asWVal().toString();
        }
        writeCall(args);
    }

    private void writeCall(String[] args) {
        out.printf("%s(", args[0]);
        for (int i = 1; i != args.length; ++i) {
            if(i != 1) {
                out.print(", ");
            }
            out.print(args[i]);
        }
        out.println(");");
    }

    // TODO: named block
    private void writeNamedBlock(int indent, Location<Bytecode.NamedBlock> b) {
        out.print(b.getBytecode().getName());
        out.println(":");
        writeBlock(indent+1,b.getBlock(0));
        throw new NotImplementedYet("named block", b);
    }

    private void writeWhile(int indent, Location<Bytecode.While> b) {
        Location<?>[] loopInvariant = b.getOperandGroup(0);
        // Location<?>[] modifiedOperands = b.getOperandGroup(1);
        String cond = writeAllocations(indent, b.getOperand(0)).as(BOOL).toString();
        loopLabels.addLast("WHILE__" + loopLabels.size());
        out.printf("CONTINUE__%s:\n", loopLabels.getLast());
        tabIndent(indent+1);
        out.printf("while (%s)", cond);
        // out.print(" modifies ");
        // writeExpressions(modifiedOperands,out);
        writeLoopInvariant(indent + 2, "invariant", loopInvariant);
        out.println();
        tabIndent(indent + 1);
        out.println("{");
        writeBlock(indent+1,b.getBlock(0));
        tabIndent(indent+1);
        out.println("}");
        tabIndent(indent+1);
        out.printf("BREAK__%s:\n", loopLabels.removeLast());
    }

    private void writeLoopInvariant(int indent, String keyword, Location<?>[] loopInvariant) {
        if (loopInvariant.length > 0) {
            for (Location<?> invariant : loopInvariant) {
                out.println();
                tabIndent(indent);
                out.printf("%s %s;", keyword, boolExpr(invariant).toString());
            }
        }
    }

    private void writeReturn(int indent, Location<Bytecode.Return> b) {
        // Boogie return does not take any expressions.
        // Instead, we must write to the result variables.
        Location<?>[] operands = b.getOperands();
        String[] args = new String[operands.length];
        for (int i = 0; i != operands.length; ++i) {
            args[i] = writeAllocations(indent, operands[i]).asWVal().toString();
        }
        for (int i = 0; i != operands.length; ++i) {
            VariableDeclaration locn = (VariableDeclaration) outDecls.get(i).getBytecode();
            String name = locn.getName();
            out.printf("%s := %s;\n", name, args[i]);
            tabIndent(indent+1);
        }
        out.println("return;");
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
        switchCount++;
        // we number each switch uniquely, so that nested switches and
        // non-nested switches in the same body all have distinct labels.
        loopLabels.addLast("SWITCH" + switchCount);
        String var = createSwitchVar(switchCount);
        Case[] cases = sw.getBytecode().cases();
        String value = writeAllocations(indent, sw.getOperand(0)).asWVal().toString();
        out.printf("%s := %s;\n", var, value);
        // build all the case labels we could jump to.
        StringBuilder labels = new StringBuilder();
        for (int i = 0; i < cases.length; i++) {
            if (i > 0) {
                labels.append(", ");
            }
            labels.append(loopLabels.getLast() + "__CASE" + i);
        }
        tabIndent(indent + 1);
        out.printf("goto %s;\n", labels.toString()); // non-deterministic
        BoogieExpr defaultCond = new BoogieExpr(BoogieType.BOOL, "true");
        for (int i = 0; i < cases.length; i++) {
            writeCase(indent + 1, var, i, cases[i], sw.getBlock(i), defaultCond);
        }
        tabIndent(indent + 1);
        // We add a 'skip' statement after the BREAK label, just in case this switch is not inside a block.
        // For example, Switch_Valid_5.whiley.
        out.printf("BREAK__%s:\n", loopLabels.removeLast());
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
        BoogieExpr var = new BoogieExpr(BoogieType.WVAL, varStr);
        BoogieExpr match = new BoogieExpr(BoogieType.BOOL);
        String op = null;
        for (Constant cd : c.values()) {
            BoogieExpr val = createConstant(cd).asWVal();
            BoogieExpr test = new BoogieExpr(BoogieType.BOOL, var, " == ", val);
            BoogieExpr negTest = new BoogieExpr(BoogieType.BOOL, var, " != ", val);
            defaultCond.addOp(" && ", negTest);
            if (op == null) {
                match = test;
            } else {
                op = " || ";
                match.addOp(op, test);
            }
        }
        tabIndent(indent + 1);
        out.printf(loopLabels.getLast() + "__CASE%d:\n",  count);
        tabIndent(indent + 2);
        BoogieExpr assume = c.values().length == 0 ? defaultCond : match;
        out.printf("assume %s;\n", assume.as(BOOL).toString());
        writeBlock(indent + 1, b);
        tabIndent(indent + 2);
        out.printf("goto BREAK__%s;\n", loopLabels.getLast());
    }

    private void writeVariableInit(int indent, Location<VariableDeclaration> loc) {
        Location<?>[] operands = loc.getOperands();
        if (operands.length > 0) {
            BoogieExpr rhs = writeAllocations(indent, operands[0]).asWVal();
            if (operands[0].getBytecode() instanceof Bytecode.Invoke
                    && ((Bytecode.Invoke) operands[0].getBytecode()).type() instanceof Type.Method) {
                out.printf("call ");
            }
            out.printf("%s := %s;\n", loc.getBytecode().getName(), rhs.toString());
        }
        // ELSE
        // TODO: Do we need a havoc here, to mimic non-det initialisation?
    }

    /** Convenience: equivalent to expr(_).as(BOOL). */
    protected BoogieExpr boolExpr(Location<?> expr) {
        return expr(expr).as(BOOL);
    }

    /** Convenience: equivalent to expr(_).as(INT). */
    protected BoogieExpr intExpr(Location<?> expr) {
        return expr(expr).as(INT);
    }

    @SuppressWarnings("unchecked")
    protected BoogieExpr expr(Location<?> expr) {
        switch (expr.getOpcode()) {
        case Bytecode.OPCODE_arraylength:
            return writeArrayLength((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_arrayindex:
            return writeArrayIndex((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_array:
            BoogieExpr[] avals = Arrays.stream(expr.getOperands()).map(this::expr).toArray(BoogieExpr[]::new);
            return createArrayInitialiser(avals);

        case Bytecode.OPCODE_arraygen:
            return writeArrayGenerator((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_convert:
            return writeConvert((Location<Bytecode.Convert>) expr);

        case Bytecode.OPCODE_const:
            Bytecode.Const c = (Bytecode.Const) expr.getBytecode();
            return createConstant(c.constant());

        case Bytecode.OPCODE_fieldload:
            return writeFieldLoad((Location<Bytecode.FieldLoad>) expr);

        case Bytecode.OPCODE_indirectinvoke:
            return writeIndirectInvokeExpr((Location<Bytecode.IndirectInvoke>) expr);

        case Bytecode.OPCODE_invoke:
            return writeInvoke((Location<Bytecode.Invoke>) expr);

        case Bytecode.OPCODE_lambda:
            return writeLambda((Location<Bytecode.Lambda>) expr);

        case Bytecode.OPCODE_record:
            BoogieExpr[] rvals = Arrays.stream(expr.getOperands()).map(this::expr).toArray(BoogieExpr[]::new);
            return createRecordConstructor((Type.EffectiveRecord) expr.getType(), rvals);

        case Bytecode.OPCODE_newobject:
            return writeNewObject((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_dereference:
            return writeDereference((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_logicalnot:
            return prefixOp(BOOL, expr, "! ", BOOL);

        case Bytecode.OPCODE_neg:
            return prefixOp(INT, expr, "- ", INT);

        case Bytecode.OPCODE_all:
            return writeQuantifier("forall", " ==> ", (Location<Bytecode.Quantifier>) expr);

        case Bytecode.OPCODE_some:
            return writeQuantifier("exists", " && ", (Location<Bytecode.Quantifier>) expr);

        case Bytecode.OPCODE_add:
            return infixOp(INT, expr, " + ", INT);

        case Bytecode.OPCODE_sub:
            return infixOp(INT, expr, " - ", INT);

        case Bytecode.OPCODE_mul:
            return infixOp(INT, expr, " * ", INT);

        case Bytecode.OPCODE_div:
            // TODO: fix this for negative numbers.
            // Boogie 'mod' implements Euclidean division, whereas Whiley uses truncated division.
            // See https://en.wikipedia.org/wiki/Modulo_operation for explanations.
            // See http://boogie.codeplex.com/discussions/397357 for what Boogie does.
            return infixOp(INT, expr, " div ", INT);

        case Bytecode.OPCODE_rem:
            // TODO: fix this for negative numbers.
            // Boogie 'mod' implements Euclidean division, whereas Whiley uses truncated division.
            // See https://en.wikipedia.org/wiki/Modulo_operation for explanations.
            // See http://boogie.codeplex.com/discussions/397357 for what Boogie does.
            return infixOp(INT, expr, " mod ", INT);

        case Bytecode.OPCODE_bitwiseinvert:
            String opType = bitwiseType(expr.getOperand(0));
            BoogieExpr lhs = expr(expr.getOperand(0)).as(INT);
            String call = String.format("%s_invert(%s)", opType, lhs.toString());
            return new BoogieExpr(INT, call);

        case Bytecode.OPCODE_bitwiseor:
            return bitwiseOp(expr, "or");
        case Bytecode.OPCODE_bitwisexor:
            return bitwiseOp(expr, "xor");
        case Bytecode.OPCODE_bitwiseand:
            return bitwiseOp(expr, "and");
        case Bytecode.OPCODE_shl:
            return bitwiseOp(expr, "shift_left");
        case Bytecode.OPCODE_shr:
            return bitwiseOp(expr, "shift_right");

        case Bytecode.OPCODE_eq:
            return writeEquality((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_ne:
            BoogieExpr eq = writeEquality((Location<Bytecode.Operator>) expr);
            BoogieExpr outNE = new BoogieExpr(BOOL);
            outNE.addOp("! ", eq);
            return outNE;

        case Bytecode.OPCODE_lt:
            return infixOp(INT, expr, " < ", BOOL);

        case Bytecode.OPCODE_le:
            return infixOp(INT, expr, " <= ", BOOL);

        case Bytecode.OPCODE_gt:
            return infixOp(INT, expr, " > ", BOOL);

        case Bytecode.OPCODE_ge:
            return infixOp(INT, expr, " >= ", BOOL);

        case Bytecode.OPCODE_logicaland:
            return infixOp(BOOL, expr, " && ", BOOL);

        case Bytecode.OPCODE_logicalor:
            return infixOp(BOOL, expr, " || ", BOOL);

        case Bytecode.OPCODE_is:
            return writeIs((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_varaccess:
            return writeVariableAccess((Location<VariableAccess>) expr);

        default:
            throw new IllegalArgumentException("unknown bytecode encountered: " + expr.getBytecode());
        }
    }

    private BoogieExpr prefixOp(BoogieType argType, Location<?> c, String op, BoogieType resultType) {
        BoogieExpr out = new BoogieExpr(resultType);
        BoogieExpr rhs = expr(c.getOperand(0)).as(argType);
        out.addOp(op, rhs);
        return out;
    }

    private BoogieExpr infixOp(BoogieType argType, Location<?> c, String op, BoogieType resultType) {
        BoogieExpr out = new BoogieExpr(resultType);
        BoogieExpr lhs = expr(c.getOperand(0)).as(argType);
        BoogieExpr rhs = expr(c.getOperand(1)).as(argType);
        out.addOp(lhs, op, rhs);
        return out;
    }

    private BoogieExpr bitwiseOp(Location<?> c, String op) {
        String opType = bitwiseType(c.getOperand(0));
        BoogieExpr lhs = expr(c.getOperand(0)).as(INT);
        BoogieExpr rhs = expr(c.getOperand(1)).as(INT);
        String call = String.format("%s_%s(%s, %s)", opType, op, lhs.toString(), rhs.toString());
        BoogieExpr out = new BoogieExpr(INT, call);
        return out;
    }

    /** We distinguish bitwise operators on byte values from other int values. */
    private String bitwiseType(Location<?> operand) {
        return operand.getType().equals(Type.T_BYTE) ? "byte" : "bitwise";
    }

    private BoogieExpr writeVariableAccess(Location<VariableAccess> loc) {
        Location<VariableDeclaration> vd = getVariableDeclaration(loc.getOperand(0));
        String name = vd.getBytecode().getName();
        return new BoogieExpr(WVAL, name);
    }

    private BoogieExpr writeArrayLength(Location<Bytecode.Operator> expr) {
        BoogieExpr out = new BoogieExpr(INT);
        out.print("arraylen(");
        out.addExpr(expr(expr.getOperand(0)).asWVal());
        out.print(")");
        return out;
    }

    private BoogieExpr writeArrayIndex(Location<Bytecode.Operator> expr) {
        BoogieExpr out = new BoogieExpr(WVAL);
        out.addExpr(expr(expr.getOperand(0)).as(ARRAY));
        out.addOp("[", intExpr(expr.getOperand(1)));
        out.print("]");
        return out;
    }

    /**
     * Whiley array generators [val;len] are represented as:
     * <pre>
     * fromArray(arrayconst(val), len)
     * </pre>
     * @param expr
     */
    private BoogieExpr writeArrayGenerator(Location<Bytecode.Operator> expr) {
        BoogieExpr out = new BoogieExpr(WVAL);
        out.print("fromArray(arrayconst(");
        out.addExpr(expr(expr.getOperand(0)).asWVal());
        out.print("), ");
        out.addExpr(expr(expr.getOperand(1)).as(INT));
        out.print(")");
        return out;
    }

    private BoogieExpr writeConvert(Location<Bytecode.Convert> expr) {
        // TODO: implement the record (and object?) conversion that drops fields?
        // See tests/valid/Coercion_Valid_9.whiley
        // TODO: are there any valid conversions in Boogie?
        // out.print("(" + expr.getType() + ") ");
        return expr(expr.getOperand(0));
    }

    private BoogieExpr writeFieldLoad(Location<Bytecode.FieldLoad> expr) {
        BoogieExpr out = new BoogieExpr(WVAL);
        out.addExpr(expr(expr.getOperand(0)).as(RECORD));
        out.printf("[%s]", mangleWField(expr.getBytecode().fieldName()));
        return out;
    }

    private BoogieExpr writeIndirectInvokeExpr(Location<Bytecode.IndirectInvoke> expr) {
        Bytecode.IndirectInvoke invoke = expr.getBytecode();
        int[] args = invoke.arguments();
        if (args.length != 1) {
            throw new NotImplementedYet("indirect invoke with " + args.length + " args", expr);
        }
        BoogieExpr func = expr(expr.getOperand(0)).as(FUNCTION);
        BoogieExpr arg = expr(expr.getOperandGroup(0)[0]).asWVal();
        BoogieExpr out = new BoogieExpr(WVAL, "applyTo1(" + func + ", " + arg + ")");
        return out;
    }

    private BoogieExpr writeInvoke(Location<Bytecode.Invoke> expr) {
        // TODO: check that it is safe to use unqualified DeclID names?
        BoogieExpr out = new BoogieExpr(WVAL);
        String name = expr.getBytecode().name().name();
        Type.FunctionOrMethod type = expr.getBytecode().type();
        if (type instanceof Type.Method) {
            // The Whiley language spec 0.3.38, Section 3.5.5, says that because they are impure,
            // methods cannot be called inside specifications.
            throw new NotImplementedYet("call to method (" + name + ") from inside an expression", expr);
        }
        out.print(mangleFunctionMethodName(name, type) + "(");
        Location<?>[] operands = expr.getOperands();
        for(int i=0;i!=operands.length;++i) {
            if(i!=0) {
                out.print(", ");
            }
            out.addExpr(expr(operands[i]).asWVal());
        }
        out.print(")");
        return out;
    }

    // TODO: lambda
    // Question: some lambda expressions capture surrounding variables - how can we represent this in Boogie?
    private BoogieExpr writeLambda(Location<Bytecode.Lambda> expr) {
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

    private BoogieExpr writeNewObject(Location<Bytecode.Operator> expr) {
        BoogieExpr be = expr(expr.getOperand(0)).asWVal();
        String ref = NEW_REF + newAllocations.size();
        // this allocation will be done just BEFORE this expression
        newAllocations.add(be.toString());
        return new BoogieExpr(WREF, ref);
    }

    private BoogieExpr writeDereference(Location<Bytecode.Operator> expr) {
        BoogieExpr be = expr(expr.getOperand(0)).as(WREF);
        // TODO: assume the type information of out.
        BoogieExpr out = new BoogieExpr(WVAL, "w__heap[" + be.toString() + "]");
        return out;
    }

    private BoogieExpr writeIs(Location<Bytecode.Operator> c) {
        BoogieExpr out = new BoogieExpr(BOOL);
        Location<?> lhs = c.getOperand(0);
        Location<?> rhs = c.getOperand(1);
        if (lhs.getBytecode() instanceof Bytecode.VariableAccess
                && rhs.getBytecode() instanceof Bytecode.Const) {
            Location<VariableDeclaration> vd = getVariableDeclaration(lhs.getOperand(0));
            final String name = vd.getBytecode().getName();
            Bytecode.Const constType = (Bytecode.Const) rhs.getBytecode();
            Constant.Type type = (Constant.Type) constType.constant();
            out.print(typePredicate(name, type.value()));
        } else {
            throw new NotImplementedYet("expr is type", c);
        }
        return out;
    }

//    private void writePrefixLocations(String resultType, String argType, Location<Bytecode.Operator> expr) {
//        // Prefix operators
//        out.print("from" + resultType + "(");
//        out.print(opcode(expr.getBytecode().kind()));
//        out.print("to" + argType + "(");
//        writeBracketedExpression(expr.getOperand(0));
//        out.print("))");
//    }
//
//    private void writeInfixLocations(String resultType, String argType, Location<Bytecode.Operator> c) {
//        out.print("from" + resultType + "(");
//        out.print("to" + argType + "(");
//        writeBracketedExpression(c.getOperand(0));
//        out.print(") ");
//        out.print(opcode(c.getBytecode().kind()));
//        out.print(" to" + argType + "(");
//        writeBracketedExpression(c.getOperand(1));
//        out.print("))");
//    }

    /**
     * Equality and inequality requires type-dependent expansion.
     *
     * @param resultType
     * @param argType
     * @param c
     */
    private BoogieExpr writeEquality(Location<Bytecode.Operator> c) {
        Location<?> left = c.getOperand(0);
        Location<?> right = c.getOperand(1);
        Type leftType = c.getOperand(0).getType();
        Type rightType = c.getOperand(1).getType();
        Type eqType = Type.intersect(leftType, rightType);
        if (!isUsableEqualityType(eqType)) {
            if (isUsableEqualityType(leftType)) {
                eqType = leftType;
            } else if (isUsableEqualityType(rightType)) {
                eqType = rightType;
            } else {
                throw new NotImplementedYet("comparison of void intersection type: " + leftType + " and " + rightType, c);
            }
        }
        BoogieExpr eq = writeTypedEquality(eqType, expr(left), expr(right)).as(BOOL);
        return eq;
    }

    /** True for the types that our equality code generator can handle. */
    private boolean isUsableEqualityType(Type type) {
        return type instanceof Type.Bool
            || type instanceof Type.Int
            || type instanceof Type.Byte
            || type instanceof Type.Null
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
    private BoogieExpr writeTypedEquality(Type eqType, BoogieExpr left, BoogieExpr right) {
        BoogieExpr out = new BoogieExpr(BOOL);
        if (eqType instanceof Type.Null) {
            // This requires special handling, since we do not have toNull and fromNull functions.
            // Instead, we just compare both sides to the WVal 'null' constant.
            // TODO: an alternative would be to just compare the WVals using '=='?
            BoogieExpr nulle = new BoogieExpr(NULL, "null");
            BoogieExpr lhs = new BoogieExpr(BOOL, left.asWVal(), " == ", nulle);
            BoogieExpr rhs = new BoogieExpr(BOOL, right.asWVal(), " == ", nulle);
            out.addOp(lhs, " && ", rhs);
        } else if (eqType instanceof Type.Int
                || eqType instanceof Type.Byte) {
            out.addOp(left.as(INT), " == ", right.as(INT));
        } else if (eqType instanceof Type.Bool) {
            out.addOp(left.as(BOOL), " == ", right.as(BOOL));
        } else if (eqType instanceof Type.Record) {
            BoogieExpr leftRec = left.as(RECORD).atom();
            BoogieExpr rightRec = right.as(RECORD).atom();
            Type.Record recType = (Type.Record) eqType;
            List<String> fields = new ArrayList<>(recType.keys());
            fields.sort(null);
            if (fields.isEmpty()) {
                out.print("true");
            }
            for (int i = 0; i < fields.size(); i++) {
                String field = fields.get(i);
                String deref = "[" + mangleWField(field) + "]";
                BoogieExpr leftVal = new BoogieExpr(WVAL, leftRec + deref);
                BoogieExpr rightVal = new BoogieExpr(WVAL, rightRec + deref);
                BoogieExpr feq = writeTypedEquality(recType.fields().get(field), leftVal, rightVal).as(BOOL);
                if (i == 0) {
                    out.addExpr(feq);
                } else {
                    out.addOp(" && ", feq);
                }
            }
        } else if (eqType instanceof Type.Array) {
            BoogieExpr leftArray = left.as(ARRAY).atom();
            BoogieExpr rightArray = right.as(ARRAY).atom();
            Type.Array arrayType = (Type.Array) eqType;
            Type elemType = arrayType.element();
            // we check the length and all the values:
            //    arraylen(left) == arraylen(right)
            //    && (forall i:int :: 0 <= i && i < arraylen(a) ==> left[i] == right[i])
            String index = generateFreshBoundVar("idx");
            String deref = "[" + index + "]";
            BoogieExpr leftVal = new BoogieExpr(WVAL, leftArray + deref);
            BoogieExpr rightVal = new BoogieExpr(WVAL, rightArray + deref);
            out.printf("arraylen(%s) == arraylen(%s) && (forall %s:int :: 0 <= %s && %s < arraylen(%s)",
                    left.asWVal().toString(),
                    right.asWVal().toString(),
                    index, index, index,
                    left.asWVal().toString());
            out.addOp(" ==> ", writeTypedEquality(elemType, leftVal, rightVal).as(BOOL));
            out.print(")");
            out.setOp(" && "); // && is outermost, since the ==> is bracketed.
        } else {
            throw new NotImplementedYet("comparison of values of type: " + eqType
                    + ".  " + left.toString() + " == " + right.toString(), null);
        }
        return out;
    }

    @SuppressWarnings("unchecked")
    private BoogieExpr writeQuantifier(String quant, String predOp, Location<Bytecode.Quantifier> c) {
        BoogieExpr decls = new BoogieExpr(BOOL);
        BoogieExpr constraints = new BoogieExpr(BOOL);
        for (int i = 0; i != c.numberOfOperandGroups(); ++i) {
            Location<?>[] range = c.getOperandGroup(i);
            if (i != 0) {
                decls.print(", ");
                constraints.print(" && ");
            }
            // declare the bound variable: v:WVal
            Location<VariableDeclaration>  v = (Location<VariableDeclaration>) range[SyntaxTree.VARIABLE];
            String name = v.getBytecode().getName();
            decls.printf("%s:WVal", name);

            // and add the constraint: isInt(v) && start <= v && v <= end
            BoogieExpr vExpr = new BoogieExpr(WVAL, name).as(INT);
            BoogieExpr start = intExpr(range[SyntaxTree.START]);
            BoogieExpr end = intExpr(range[SyntaxTree.END]);
            constraints.print("isInt(" + name + ")");
            constraints.addOp(" && ", new BoogieExpr(BOOL, start, " <= ", vExpr));
            constraints.addOp(" && ", new BoogieExpr(BOOL, vExpr, " < ", end));
        }
        BoogieExpr out = new BoogieExpr(BOOL);
        out.printf("(%s %s :: ", quant, decls.toString());
        out.addOp(constraints, predOp, boolExpr(c.getOperand(SyntaxTree.CONDITION)));
        out.print(")");
        return out;
    }

    protected void tabIndent(int indent) {
        indent = indent * 4;
        for(int i=0;i<indent;++i) {
            out.print(" ");
        }
    }

    /** Returns an indent of the requested number of 'tab' stops. */
    protected String makeIndent(int indent) {
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
        if (type instanceof Type.Nominal) {
            String typeName = ((Type.Nominal) type).name().name();
            return typePredicateName(typeName) + "(" + var + ")";
        }
        if (type instanceof Type.Int) {
            return "isInt(" + var + ")";
        }
        if (type instanceof Type.Byte) {
            return "isByte(" + var + ")";
        }
        if (type instanceof Type.Null) {
            return "isNull(" + var + ")";
        }
        if (type instanceof Type.Bool) {
            return "isBool(" + var + ")";
        }
        if (type instanceof Type.Any) {
            return "true";
        }
        if (type instanceof Type.Array) {
            Type.Array t = (Type.Array) type;
            Type elemType = t.element();
            String bndVar = generateFreshBoundVar("i__");
            String elem = "toArray(" + var + ")[" + bndVar + "]";
            return String.format("isArray(%s) && (forall %s:int :: 0 <= %s && %s < arraylen(%s) ==> %s)",
                    var, bndVar, bndVar, bndVar, var, typePredicate(elem, elemType));
        }
        //		if (type instanceof Type.Void) {
        //			// this should not happen?
        //		}
        if (type instanceof Type.Record) {
            Type.Record t = (Type.Record) type;
            Map<String, Type> fields = t.fields();
            // add constraints about the fields
            final String objrec;
            //if (t.isOpen()) {
            //	objrec = "Object(" + var + ")";
            //} else {
            objrec = "Record(" + var + ")";
            //}
            final StringBuilder result = new StringBuilder();
            result.append("is" + objrec);
            for (Map.Entry<String, Type> field : fields.entrySet()) {
                result.append(" && ");
                String elem = "to" + objrec + "[" + mangleWField(field.getKey()) + "]";
                Type elemType = field.getValue();
                result.append(typePredicate(elem, elemType));
            }
            return result.toString();
        }
        if (type instanceof Type.Union) {
            // we generate the disjunction of all the bounds
            Type.Union u = (Type.Union) type;
            String result = "((";
            String sep = "";
            for (Type element : u.bounds()) {
                result += sep + typePredicate(var, element);
                sep = ") || (";
            }
            return result + "))";
        }
        if (type instanceof Type.Negation) {
            // we negate the type test
            Type.Negation t = (Type.Negation) type;
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
        Type type = cd.type();
        if (cd instanceof Constant.Integer) {
            return new BoogieExpr(INT, cd.toString());
        } else if (cd instanceof Constant.Bool) {
            return new BoogieExpr(BOOL, cd.toString());
        } else if (cd instanceof Constant.Byte) {
            Constant.Byte b = (Constant.Byte) cd;
            int val = Byte.toUnsignedInt(b.value());
            return new BoogieExpr(INT, Integer.toString(val));
        } else if (cd instanceof Constant.Array) {
            Constant.Array aconst = (Constant.Array) cd;
            BoogieExpr[] values = aconst.values().stream().map(this::createConstant).toArray(BoogieExpr[]::new);
            return createArrayInitialiser(values);
        } else if (cd instanceof Constant.Null) {
            return new BoogieExpr(WVAL, "null"); // already a WVal
        } else if (cd instanceof Constant.Record) {
            Constant.Record rec = (Constant.Record) cd;
            List<String> fields = new ArrayList<String>(rec.values().keySet());
            Collections.sort(fields); // sort fields alphabetically
            BoogieExpr[] vals = fields.stream().map(f -> createConstant(rec.values().get(f))).toArray(BoogieExpr[]::new);
            return createRecordConstructor((Type.EffectiveRecord) cd.type(), vals);
        } else if (cd instanceof Constant.FunctionOrMethod) {
            Constant.FunctionOrMethod fm = (Constant.FunctionOrMethod) cd;
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
        BoogieExpr out = new BoogieExpr(WVAL);
        out.print("fromArray(arrayconst(");
        if (values.length == 0) {
            out.print("null"); // the type of values should be irrelevant
        } else {
            out.addExpr(values[0].asWVal());
        }
        out.print(")");
        for (int i = 1; i < values.length; ++i) {
            out.print("[" + i + " := ");
            out.addExpr(values[i].asWVal()); // no brackets needed
            out.print("]");
        }
        out.print(", ");
        out.print(Integer.toString(values.length));
        out.print(")");
        return out;
    }

    private BoogieExpr createRecordConstructor(Type.EffectiveRecord type, BoogieExpr[] values) {
        BoogieExpr out = new BoogieExpr(RECORD);
        List<String> fields = new ArrayList<String>(type.fields().keySet());
        // the values are presented in order according to the alphabetically sorted field names!
        Collections.sort(fields);
        out.print("empty__record");
        for(int i = 0; i != values.length; ++i) {
            out.printf("[%s := %s]", mangleWField(fields.get(i)), values[i].asWVal().toString());
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
    protected String mangleWField(String field) {
        return "$" + field;
    }

    /**
     * Determines which functions/methods need renaming to resolve overloading.
     *
     * This should be called once at the beginning of each file/module.
     *
     * @param functionOrMethods
     */
    private void resolveFunctionOverloading(Collection<WyilFile.FunctionOrMethod> functionOrMethods) {
        // some common types
        List<Type> any1 = Collections.singletonList(Type.T_ANY);
        List<Type> bool1 = Collections.singletonList(Type.T_BOOL);
        List<Type> int1 = Collections.singletonList(Type.T_INT);
        List<Type> array1 = Collections.singletonList(Type.T_ARRAY_ANY);
        List<Type> ref1 = Collections.singletonList(Type.Reference(Type.T_ANY, "*"));
        List<Type> record1 = Collections.singletonList(Type.Record(false, Collections.emptyMap()));
        List<Type> object1 = Collections.singletonList(Type.Record(true, Collections.emptyMap()));
        // the following types are approximate - the params or returns are more specific than needed.
        Type.FunctionOrMethod typePredicate = Type.Function(bool1, any1);
        Type.FunctionOrMethod castFunction = Type.Function(any1, any1);
        Type.FunctionOrMethod anyMethod = Type.Method(any1, Collections.emptySet(), Collections.emptyList(), any1);

        functionOverloads = new HashMap<>();

        // Now predefine all the functions in wval.bpl (as unmangled).
        // This is so that any user-defined functions with those names will be forced to use mangled names!
        for (String predef : new String[] {
                "isNull", "isInt", "isBool", "isArray", "isRecord",
                "isObject", "isRef", "isFunction", "isMethod", "isByte",
                }) {

            predefinedFunction(predef, typePredicate);
        }
        for (String predef : new String[] {
                "toNull", "toInt", "toBool", "toArray", "toRecord",
                "toObject", "toRef", "toFunction", "toMethod", "toByte",
                }) {
            predefinedFunction(predef, castFunction);
        }
        predefinedFunction("fromInt", Type.Function(any1, int1));
        predefinedFunction("fromBool", Type.Function(any1, bool1));
        predefinedFunction("fromArray", Type.Function(any1, array1));
        predefinedFunction("fromRecord", Type.Function(any1, record1));
        predefinedFunction("fromObject", Type.Function(any1, object1));
        predefinedFunction("fromRef", Type.Function(any1, ref1));
        predefinedFunction("fromFunction", Type.Function(any1, Collections.singletonList(castFunction)));
        predefinedFunction("fromMethod", Type.Function(any1, Collections.singletonList(anyMethod)));
        predefinedFunction("applyTo1", Type.Function(any1, any1)); // should take TWO inputs

        for (WyilFile.FunctionOrMethod m : functionOrMethods) {
            String name = m.name();
            Map<Type.FunctionOrMethod, String> map = functionOverloads.get(name);
            if (map == null) {
                // first one with this name needs no mangling!
                map = new HashMap<>();
                map.put(m.type(), name);
                functionOverloads.put(name, map);
            } else if (!map.containsKey(m.type())) {
                String mangled = name + "$" + (map.size() + 1);
                map.put(m.type(), mangled);
                System.err.printf("mangle %s : %s to %s\n", name, m.type().toString(), mangled);
            }
        }
    }

    private void predefinedFunction(String predef, wyil.lang.Type.FunctionOrMethod type) {
        Map<Type.FunctionOrMethod, String> map = new HashMap<>();
        // System.err.printf("ADDING %s : %s as predefined.\n", predef, type);
        map.put(type, predef); // no name mangling, because this is a predefined function.
        functionOverloads.put(predef, map);
    }

    /**
     * Mangles a function/method name, so that simple overloaded functions are possible.
     *
     * Note that we currently ignore module names here, as it is not obvious how to get the
     * DeclID or the module of a function or method declaration.  This may become an issue
     * if we start verifying multi-module programs.
     *
     * @param method
     * @return a human-readable name for the function/method.
     */
    protected String mangleFunctionMethodName(String name, Type.FunctionOrMethod type) {
        Map<Type.FunctionOrMethod, String> map = functionOverloads.get(name);
        if (map == null) {
            System.err.printf("Warning: function/method %s : %s assumed to be external, so not mangled.\n",
                    name, type);
            return name;  // no mangling!
        }
        String result = map.get(type);
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
            Type.Record t = (Type.Record) type;
            declareNewFields(t.fields().keySet());
        } else if (type instanceof Type.Array) {
            Type.Array t = (Type.Array) type;
            done.add(t);
            declareFields(t.element(), done);
        } else if (type instanceof Type.Reference) {
            Type.Reference t = (Type.Reference) type;
            done.add(t);
            declareFields(t.element(), done);
        } else if (type instanceof Type.Negation) {
            Type.Negation t = (Type.Negation) type;
            done.add(t);
            declareFields(t.element(), done);
        } else if (type instanceof Type.Union) {
            Type.Union t = (Type.Union) type;
            done.add(t);
            for (Type b : t.bounds()) {
                declareFields(b, done);
            }
        } else if (type instanceof Type.FunctionOrMethod) {
            Type.FunctionOrMethod t = (Type.FunctionOrMethod) type;
            done.add(t);
            for (Type b : t.params()) {
                declareFields(b, done);
            }
            for (Type b : t.returns()) {
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
        for (Location<?> loc : tree.getLocations()) {
            Type[] types = loc.getTypes();
            for (Type t : types) {
                declareFields(t, new HashSet<Type>());
            }
        }
    }

    /** Walks recursively through a constant and declares any function constants. */
    private void declareFuncConstants(Constant cd) {
        if (cd instanceof Constant.Array) {
            Constant.Array aconst = (Constant.Array) cd;
            for (Constant c : aconst.values()) {
                declareFuncConstants(c);
            }
        } else if (cd instanceof Constant.Record) {
            Constant.Record rec = (Constant.Record) cd;
            for (Constant c : rec.values().values()) {
                declareFuncConstants(c);
            }
        } else if (cd instanceof Constant.FunctionOrMethod) {
            Constant.FunctionOrMethod fm = (Constant.FunctionOrMethod) cd;
            declareNewFunction(fm.name(), fm.type());
        }
    }

    /** Walks through bytecode and declares any function constants. */
    private void declareFuncConstants(SyntaxTree tree) {
        List<Location<?>> locations = tree.getLocations();
        for (int i = 0; i != locations.size(); ++i) {
            Location<?> loc = locations.get(i);
            if (loc.getBytecode().getOpcode() == Bytecode.OPCODE_const
              && ((Bytecode.Const) loc.getBytecode()).constant() instanceof Constant.FunctionOrMethod) {
                Bytecode.Const con = (Bytecode.Const) loc.getBytecode();
                Constant.FunctionOrMethod bc = (Constant.FunctionOrMethod) con.constant();
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
        uniqueId++;
        return base + uniqueId;
    }

    /**
     * Run the Whiley Compiler with the given list of arguments.
     *
     * @param args
     *            --- list of command-line arguments to provide to the Whiley
     *            Compiler.
     * @return
     */
    public static Pair<Integer,String> compile(String... args) {
        ByteArrayOutputStream syserr = new ByteArrayOutputStream();
        ByteArrayOutputStream sysout = new ByteArrayOutputStream();
        int exitCode = new WycMain(new WycBuildTask(), WycMain.DEFAULT_OPTIONS, sysout, syserr)
                .run(args);
        byte[] errBytes = syserr.toByteArray();
        byte[] outBytes = sysout.toByteArray();
        String output = new String(errBytes) + new String(outBytes);
        return new Pair<Integer,String>(exitCode,output);
    }

    /**
     * Execute a given WyIL file using the default interpreter.
     *
     * @param wyilDir
     *            The root directory to look for the WyIL file.
     * @param id
     *            The name of the WyIL file
     * @throws IOException
     */
    public static void execWyil(String wyilDir, Path.ID id) throws IOException {
        Type.Method sig = Type.Method(Collections.<Type>emptyList(), Collections.<String>emptySet(),
                Collections.<String>emptyList(), Collections.<Type>emptyList());
        NameID name = new NameID(id,"test");
        Build.Project project = initialiseProject(wyilDir);
        new Interpreter(project,null).execute(name,sig);
    }

    /**
     * The purpose of the binary file filter is simply to ensure only binary
     * files are loaded in a given directory root. It is not strictly necessary
     * for correct operation, although hopefully it offers some performance
     * benefits.
     */
    public static final FileFilter wyilFileFilter = new FileFilter() {
        @Override
        public boolean accept(File f) {
            return f.getName().endsWith(".wyil") || f.isDirectory();
        }
    };

    private static Build.Project initialiseProject(String wyilDir) throws IOException {
        Content.Registry registry = new Registry();
        DirectoryRoot wyilRoot = new DirectoryRoot(".",wyilFileFilter,registry);
        ArrayList<Path.Root> roots = new ArrayList<Path.Root>();
        roots.add(wyilRoot);
        return new StdProject(roots);
    }

    /**
     * Take a Whiley or WyIL file and convert it to Boogie.
     *
     * @param args
     * @throws IOException
     */
    public static void main(String[] args) throws IOException {
        int argnum = 0;
        boolean verbose = false;
        if (args.length > argnum && "-v".equals(args[argnum])) {
            verbose = true;
            System.out.println("Current directory is " + System.getProperty("user.dir"));
            argnum++;
        }
        if (args.length == argnum) {
            System.err.println("Usage: [-v] file.whiley or file.wyil");
            System.exit(1);
        }
        String path = args[argnum];
        boolean removeWyil = false;
        if (path.endsWith(".whiley")) {
            // System.out.println("compiling " + path);
            removeWyil = true;
            Pair<Integer,String> ok = compile(path);
            if (ok.first() != 0) {
                System.err.println("Error compiling " + path);
                System.err.println(ok.second());
                System.exit(2);
            }
            path = path.replaceAll("\\.whiley", ".wyil");
            // System.out.println("path set to " + path);
        }
        if (path.endsWith(".wyil")) {
            String bplPath = path.substring(0, path.length() - 5) + ".bpl";
            // System.out.println("loading " + path);
            try {
                PrintWriter out = new PrintWriter(new File(bplPath));
                FileInputStream fin = new FileInputStream(path);
                WyilFile wf = new WyilFileReader(fin).read();
                Wyil2Boogie translator = new Wyil2Boogie(out);
                translator.setVerbose(verbose);
                translator.apply(wf);
                if (removeWyil) {
                    // try to remove the temporary .wyil file that we created
                    new File(path).delete();
                }
            } catch (InternalFailure e) {
                e.outputSourceError(System.err);
                e.printStackTrace(System.err);
                System.exit(6);
            } catch (SyntaxError e) {
                e.outputSourceError(System.err);
                System.exit(5);
            }
            catch (RuntimeException e) {
                e.printStackTrace(System.err);
                System.exit(4);
            }
        } else {
            System.err.println("ERROR: Unknown file: " + path);
            System.exit(3);
        }
    }
}
