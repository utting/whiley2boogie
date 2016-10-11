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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
import wyil.lang.Bytecode.Expr;
import wyil.lang.Bytecode.Stmt;
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
 * TODO: mangle Whiley var names to avoid Boogie reserved words and keywords?
 *
 * TODO: change do-while translation so that invariant is not checked before first loop.
 *
 * TODO: generate in-context assertions for function preconditions, array bounds, etc.
 *
 * TODO: implement missing language features, such as:
 * <ul>
 *   <li>references, new, and dereferencing</li>
 *   <li>bitwise operators</li>
 *   <li>functions/methods with multiple return values</li>
 *   <li>lambda functions</li>
 *   <li>continue statements and named blocks</li>
 *   <li>switch</li>
 *   <li>indirect invoke</li>
 *   <li>some kinds of complex constants</li>
 * </ul>
 *
 * @author David J. Pearce
 * @author Mark Utting
 */
public final class Wyil2Boogie {
    private static final String IMMUTABLE_INPUT = "__0";

    /** The conjunction operator for pre/post conditions. */
    private static final String AND_OUTER = " &&\n      ";

    /** This is appended to each function/method name, for the precondition of that function. */
    private static final String METHOD_PRE = "__pre";

    /** Special boolean variable used to emulate do-while loops. */
    private static final Object DO_WHILE_VAR = "do__while";

    /** Where the Boogie output is written. */
    protected PrintWriter out;

    /** If true, then the Whiley bytecodes are printed as comments. */
    protected boolean verbose = false;

    /** Keeps track of which (non-mangled) WField names have already been declared. */
    private Set<String> declaredFields = new HashSet<>();

    /** Used to generate unique IDs for bound variables. */
    private int uniqueId = 0;

    /** Keeps track of the mangled names for every function and method. */
    private Map<String, Map<Type.FunctionOrMethod, String>> functionOverloads;

    /** Input parameters of the current function/method. */
    List<Location<?>> inDecls;

    /** Output parameters of the current function/method. */
    List<Location<?>> outDecls;

    public Wyil2Boogie(PrintWriter writer) {
        this.out = writer;
    }

    public Wyil2Boogie(OutputStream stream) {
        this.out = new PrintWriter(new OutputStreamWriter(stream));
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

    // ======================================================================
    // Apply Method
    // ======================================================================

    public void apply(WyilFile module) throws IOException {
        resolveFunctionOverloading(module.functionOrMethods());
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
        out.println("const " + cd.name() + " : WVal;");
        out.println("axiom " + cd.name() + " == " + createConstant(cd.constant()).asWVal() + ";");
        out.println();
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
        Map<String, Type> locals = new LinkedHashMap<>(); // preserve order, but remove duplicates
        writeLocalVarDeclsRecursive(locs, locs.size() - 1, locals);
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
                out.print("var ");
                out.print(name);
                out.print(" : WVal where ");
                out.print(typePredicate(name, decl.getType()));
                out.println(";");
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
            // loop through all child blocks
            Stmt code = (Stmt) bytecode;
            for (int b : code.getBlocks()) {
                writeLocalVarDeclsRecursive(locs, b, done);
            }
        }
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
            writeAssert(indent, (Location<Bytecode.Assert>) c);
            break;
        case Bytecode.OPCODE_assume:
            writeAssume(indent, (Location<Bytecode.Assume>) c);
            break;
        case Bytecode.OPCODE_assign:
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
            writeIf(indent, (Location<Bytecode.If>) c);
            break;
        case Bytecode.OPCODE_indirectinvoke:
            writeIndirectInvoke(indent, (Location<Bytecode.IndirectInvoke>) c);
            break;
        case Bytecode.OPCODE_invoke:
            out.print("call "); // it should be a method, not a function
            writeInvoke(indent, (Location<Bytecode.Invoke>) c);
            break;
        case Bytecode.OPCODE_namedblock:
            writeNamedBlock(indent, (Location<Bytecode.NamedBlock>) c);
            break;
        case Bytecode.OPCODE_while:
            writeWhile(indent, (Location<Bytecode.While>) c);
            break;
        case Bytecode.OPCODE_return:
            writeReturn(indent, (Location<Bytecode.Return>) c);
            break;
        case Bytecode.OPCODE_skip:
            writeSkip(indent, (Location<Bytecode.Skip>) c);
            break;
        case Bytecode.OPCODE_switch:
            writeSwitch(indent, (Location<Bytecode.Switch>) c);
            break;
        case Bytecode.OPCODE_vardecl:
        case Bytecode.OPCODE_vardeclinit:
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

    private void writeAssert(int indent, Location<Bytecode.Assert> c) {
        out.printf("assert %s;\n", boolExpr(c.getOperand(0)).toString());
    }

    private void writeAssume(int indent, Location<Bytecode.Assume> c) {
        out.printf("assume %s;\n", boolExpr(c.getOperand(0)).toString());
    }

    // TODO: handle more complex updates, like a[i][j] = val and a[i].foo = val;
    private void writeAssign(int indent, Location<Bytecode.Assign> stmt) {
        Location<?>[] lhs = stmt.getOperandGroup(SyntaxTree.LEFTHANDSIDE);
        Location<?>[] rhs = stmt.getOperandGroup(SyntaxTree.RIGHTHANDSIDE);
        if (lhs[0].getBytecode().getOpcode() == Bytecode.OPCODE_arrayindex) {
            if (lhs.length > 1) {
                throw new NotImplementedYet("Multiple array assignments not handled yet.", stmt);
            }
            // Instead of a[e] := rhs, we do a := a[e := rhs];
            assert lhs[0].numberOfOperands() == 2;
            Location<?> array = lhs[0].getOperand(0);
            if (!(array.getBytecode() instanceof Bytecode.VariableAccess)) {
                throw new NotImplementedYet("array update of complex expression", stmt);
            }
            String wval = expr(array).asWVal().toString();
            String a = expr(array).as(ARRAY).toString();
            String index = intExpr(lhs[0].getOperand(1)).toString();
            String value = expr(rhs[0]).asWVal().toString();
            out.printf("%s := fromArray(%s[%s := %s], arraylen(%s))", wval, a, index, value, wval);
        } else if (lhs[0].getBytecode().getOpcode() == Bytecode.OPCODE_fieldload) {
            if (lhs.length > 1) {
                throw new NotImplementedYet("Multiple record assignments not handled yet.", stmt);
            }
            // Instead of a[e] := rhs, we do a := a[e := rhs];
            assert lhs[0].numberOfOperands() == 1;
            Location<?> rec = lhs[0].getOperand(0);
            String field = ((Bytecode.FieldLoad) (lhs[0].getBytecode())).fieldName();
            if (!(rec.getBytecode() instanceof Bytecode.VariableAccess)) {
                throw new NotImplementedYet("record update of complex expression", stmt);
            }
            String wval = expr(rec).asWVal().toString();
            String r = expr(rec).as(RECORD).toString();
            String value = expr(rhs[0]).asWVal().toString();
            out.printf("%s := fromRecord(%s[%s := %s])", wval, r, mangleWField(field), value);
        } else {
            if (isMethod(rhs[0])) {
                // Boogie distinguishes method & function calls!
                out.print("call ");
            }
            if(lhs.length > 0) {
                for(int i = 0; i != lhs.length; ++i) {
                    if(i != 0) {
                        out.print(", ");
                    }
                    out.print(expr(lhs[i]).asWVal().toString());
                }
                out.print(" := ");
            }
            for (int i = 0; i != rhs.length; ++i) {
                if (i != 0) {
                    out.print(", ");
                }
                out.print(expr(rhs[i]).asWVal().toString());
            }
        }
        out.println(";");
    }

    private boolean isMethod(Location<?> loc) {
        if (loc.getBytecode().getOpcode() == Bytecode.OPCODE_invoke
                && ((Bytecode.Invoke)loc.getBytecode()).type() instanceof Type.Method) {
            return true;
        }
        return false;
    }

    private void writeBreak(int indent, Location<Bytecode.Break> b) {
        out.println("break;");
    }

    // TODO: implement continue by breaking out of a labelled block?
    // But 'continue' is used to carry on to next case of switch too, which requires different handling!
    private void writeContinue(int indent, Location<Bytecode.Continue> b) {
        out.println("continue;");
        throw new NotImplementedYet("continue", b);
    }

    private void writeDebug(int indent, Location<Bytecode.Debug> b) {
        // out.println("debug;");
    }

    /**
     * Generate Boogie code for do-while.
     *
     * NOTE: Boogie does not have a do{S}while(C) command,
     * so we generate a while loop and use a boolean variable to force entry the first time.
     *
     * @param indent
     * @param b
     */
    private void writeDoWhile(int indent, Location<Bytecode.DoWhile> b) {
        Location<?>[] loopInvariant = b.getOperandGroup(0);
        // Location<?>[] modifiedOperands = b.getOperandGroup(1);
        out.printf("%s := true;\n", DO_WHILE_VAR);
        tabIndent(indent+1);
        out.printf("while (%s || %s)", DO_WHILE_VAR, boolExpr(b.getOperand(0)).toString());
        writeLoopInvariant(indent + 2, loopInvariant);
        out.println();
        tabIndent(indent+1);
        out.println("{");
        tabIndent(indent+2);
        out.printf("%s := false;\n", DO_WHILE_VAR);
        writeBlock(indent+1, b.getBlock(0));
        tabIndent(indent+1);
        out.println("}");
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
        out.printf("if (%s) {\n", boolExpr(b.getOperand(0)).toString());
        writeBlock(indent+1,b.getBlock(0));
        if (b.numberOfBlocks() > 1) {
            tabIndent(indent+1);
            out.println("} else {");
            writeBlock(indent+1,b.getBlock(1));
        }
        tabIndent(indent+1);
        out.println("}");
    }

    // TODO: decide how to encode indirect calls
    private void writeIndirectInvoke(int indent, Location<Bytecode.IndirectInvoke> stmt) {
        Location<?>[] operands = stmt.getOperands();
        out.print(expr(operands[0]).toString());
        out.print("(");
        for(int i=1;i!=operands.length;++i) {
            if(i!=1) {
                out.print(", ");
            }
            out.print(expr(operands[i]).asWVal().toString());
        }
        out.println(")");
    }

    private void writeInvoke(int indent, Location<Bytecode.Invoke> stmt) {
        out.print(mangleFunctionMethodName(stmt.getBytecode().name().name(), stmt.getBytecode().type()) + "(");
        Location<?>[] operands = stmt.getOperands();
        for(int i=0;i!=operands.length;++i) {
            if(i!=0) {
                out.print(", ");
            }
            out.print(expr(operands[i]).asWVal().toString());
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
        out.printf("while (%s)", boolExpr(b.getOperand(0)).toString());
        // out.print(" modifies ");
        // writeExpressions(modifiedOperands,out);
        writeLoopInvariant(indent + 2, loopInvariant);
        out.println();
        tabIndent(indent + 1);
        out.println("{");
        writeBlock(indent+1,b.getBlock(0));
        tabIndent(indent+1);
        out.println("}");
    }

    private void writeLoopInvariant(int indent, Location<?>[] loopInvariant) {
        if (loopInvariant.length > 0) {
            for (Location<?> invariant : loopInvariant) {
                out.println();
                tabIndent(indent);
                out.printf("invariant %s;", boolExpr(invariant).toString());
            }
        }
    }

    private void writeReturn(int indent, Location<Bytecode.Return> b) {
        // Boogie return does not take any expressions.
        // Instead, we must write to the result variables.
        Location<?>[] operands = b.getOperands();
        for (int i = 0; i != operands.length; ++i) {
            VariableDeclaration locn = (VariableDeclaration) outDecls.get(i).getBytecode();
            String name = locn.getName();
            out.printf("%s := %s;\n", name, expr(operands[i]).asWVal().toString());
            tabIndent(indent+1);
        }
        out.println("return;");
    }

    private void writeSkip(int indent, Location<Bytecode.Skip> b) {
        // no output needed.  Boogie uses {...} blocks, so empty statements are okay.
    }

    // TODO: switch
    private void writeSwitch(int indent, Location<Bytecode.Switch> b) {
        throw new NotImplementedYet("switch", b);
    }

    private void writeVariableInit(int indent, Location<VariableDeclaration> loc) {
        Location<?>[] operands = loc.getOperands();
        // out.print(loc.getType());
        // out.print(" ");
        if (operands.length > 0) {
            out.print(loc.getBytecode().getName());
            out.print(" := ");
            out.print(expr(operands[0]).asWVal().toString());
            out.println(";");
        }
        // ELSE
        // TODO: Do we need a havoc here, to mimic non-det initialisation?
    }

    /** Convenience: equivalent to expr(_).as(BOOL). */
    private BoogieExpr boolExpr(Location<?> expr) {
        return expr(expr).as(BOOL);
    }

    /** Convenience: equivalent to expr(_).as(INT). */
    private BoogieExpr intExpr(Location<?> expr) {
        return expr(expr).as(INT);
    }

    @SuppressWarnings("unchecked")
    private BoogieExpr expr(Location<?> expr) {
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
            return writeIndirectInvoke((Location<Bytecode.IndirectInvoke>) expr);

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
            // TODO: dereference
            throw new NotImplementedYet("dereference", expr);

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
        case Bytecode.OPCODE_bitwiseor:  // TODO
        case Bytecode.OPCODE_bitwisexor: // TODO
        case Bytecode.OPCODE_bitwiseand: // TODO
        case Bytecode.OPCODE_shl:        // TODO
        case Bytecode.OPCODE_shr:        // TODO
            throw new NotImplementedYet("bitwise operators not supported yet: " + expr.getBytecode(), expr);

        case Bytecode.OPCODE_eq:
            return writeEquality((Location<Bytecode.Operator>) expr);

        case Bytecode.OPCODE_ne:
            BoogieExpr eq = writeEquality((Location<Bytecode.Operator>) expr);
            BoogieExpr out = new BoogieExpr(BOOL);
            out.addOp("! ", eq);
            return out;

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

    // TODO:
    private BoogieExpr writeIndirectInvoke(Location<Bytecode.IndirectInvoke> expr) {
        throw new NotImplementedYet("indirect invoke", expr);
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
    }

    // TODO: new object
    private BoogieExpr writeNewObject(Location<Bytecode.Operator> expr) {
        //out.print("new ");
        //writeExpression(expr.getOperand(0));
        throw new NotImplementedYet("new record/object", expr);
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
        // first pass just declares the bound variables
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

    private void tabIndent(int indent) {
        indent = indent * 4;
        for(int i=0;i<indent;++i) {
            out.print(" ");
        }
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
    private String mangleFunctionMethodName(String name, Type.FunctionOrMethod type) {
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
