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

import java.io.*;
import java.util.*;

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
import wyil.lang.Type.Method;
import wyil.lang.Bytecode.AliasDeclaration;
import wyil.lang.Bytecode.Expr;
import wyil.lang.Bytecode.VariableAccess;
import wyil.lang.Bytecode.VariableDeclaration;
import wyil.lang.Constant;
import wyil.lang.SyntaxTree.Location;
import wyil.lang.WyilFile.*;
import wyil.util.interpreter.Interpreter;
import wyc.WycMain;
import wyc.util.WycBuildTask;

/**
 * Translates WYIL bytecodes into Boogie and outputs into a given file.
 *
 * <b>NOTE:</b> the output file is put in the same place as the
 * Whiley file, but with the file extension ".bpl".
 *
 * @author David J. Pearce
 * @author Mark Utting
 *
 */
public final class Wyil2Boogie {
	private PrintWriter out;
	private boolean verbose = false;

	/** Input parameters of current function/procedure. */
	List<Location<?>> inDecls;

	/** Output parameters of current function/procedure. */
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

	// ======================================================================
	// Apply Method
	// ======================================================================

	public void apply(WyilFile module) throws IOException {
		out.println();
		for(WyilFile.Constant cd : module.constants()) {
			writeConstant(cd);
		}
		if(!module.constants().isEmpty()) {
			out.println();
		}
		for (WyilFile.Type td : module.types()) {
			writeTypeSynonym(td);
		}

		for(FunctionOrMethod md : module.functionOrMethods()) {
			writeProcedure(md);
			out.println();
		}
		out.flush();
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
		// writeModifiers(td.modifiers());
		String param = "x";
		if (!td.getTree().getLocations().isEmpty()) {
			@SuppressWarnings("unchecked")
			Location<VariableDeclaration> loc = (Location<VariableDeclaration>) td.getTree().getLocation(0);
			param = loc.getBytecode().getName();
		}
		out.print("function " + typePredicateName(td.name()) + "(" + param + ":WVal) returns (bool) { ");
		out.print(typePredicate(param, t));
		if (!td.getInvariant().isEmpty()) {
			out.print(" && (");
			writeConjunction(td.getInvariant());
			out.println(")");
		}
		out.println(" }");
	}

	private void writeConstant(WyilFile.Constant cd) {
		if(verbose) {
			writeLocationsAsComments(cd.getTree());
		}
		out.println("const " + cd.name() + " : WVal;");
		out.println("axiom " + cd.name() + " == " + createConstant(cd.constant()) + ";");
		out.println();
	}

	private void writeProcedure(FunctionOrMethod method) {
		if(verbose) {
			writeLocationsAsComments(method.getTree());
		}
		Type.FunctionOrMethod ft = method.type();
		String name = method.name();
		int inSize = ft.params().size();
		int outSize = ft.returns().size();
		inDecls = method.getTree().getLocations().subList(0, inSize);
		outDecls = method.getTree().getLocations().subList(inSize, inSize + outSize);
		assert inDecls.size() == inSize;
		assert outDecls.size() == outSize;
		if (ft instanceof Type.Function) {
			// We generate a Boogie function, as well as a procedure.
			// The procedure is used to verify the code against pre/post.
			// The function encodes just the pre=>post properties.
			// This is because Boogie functions cannot include code,
			// they are uninterpreted functions or with an expression body only.
			writeFunction(method);
			name = name + "__impln";
		}
		out.print("procedure ");
		writeSignature(name, method, true);
		out.print(";");
		for (Location<Expr> precondition : method.getPrecondition()) {
			out.println();
			out.print("requires toBool(");
			writeExpression(precondition);
			out.print(");");
		}
		for (Location<Expr> postcondition : method.getPostcondition()) {
			out.println();
			out.print("ensures toBool(");
			writeExpression(postcondition);
			out.print(");");
		}
		out.println();
		out.print("implementation ");
		writeSignature(name, method, false);
		if (method.getBody() != null) {
			out.println();
			out.println("{");
			writeLocalVarDecls(method.getTree().getLocations());
			writeBlock(0, method.getBody());
			out.println("}");
		}
	}

	/**
	 * Writes out a Boogie function declaration, plus a pre implies post axiom.
	 *
	 * @param method
	 * @param out
	 */
	private void writeFunction(FunctionOrMethod method) {
		assert method.isFunction();
		out.print("function ");
		out.print(method.name());
		out.print("(");
		writeParameters(method.type().params(), inDecls, false);
		if (!method.type().returns().isEmpty()) {
			out.print(") returns (");
			writeParameters(method.type().returns(), outDecls, false);
		}
		out.println(");");

		// write pre => post axiom
		out.print("axiom (forall ");
		writeParameters(method.type().params(), inDecls, false);
		if (inDecls.size() > 0 && outDecls.size() > 0) {
			out.print(", ");
		}
		writeParameters(method.type().returns(), outDecls, false);
		out.println(" :: ");
		out.print("\t(");
		// TODO: may need more brackets!
		writeConjunction(method.getPrecondition());
		out.print(")\n\t==> (");
		writeConjunction(method.getPostcondition());
		out.println("));");
		out.println();
	}

	/**
	 * Writes a conjunction, and leaves it as a Boogie boolean value.
	 *
	 * @param preds
	 */
	private void writeConjunction(List<Location<Bytecode.Expr>> preds) {
		if (preds.isEmpty()) {
			out.print("true");
		} else if (preds.size() == 1) {
			// we must convert it from WVal to a Boogie boolean value
			out.print("toBool(");
			writeExpression(preds.get(0));
			out.print(")");
		} else {
			writeExpressions(preds.toArray(new Location<?>[0]), " && ");
		}
	}

	private void writeSignature(String name, FunctionOrMethod method, boolean full) {
		out.print(name);
		out.print("(");
		writeParameters(method.type().params(), inDecls, full);
		if (!method.type().returns().isEmpty()) {
			out.print(") returns (");
			writeParameters(method.type().returns(), outDecls, full);
		}
		out.print(")");
	}

	/**
	 * Writes just the declarations and type constraints of local variables.
	 *
	 * This is done only at the top level of each procedure.
	 *
	 * @param locs
	 * @param out
	 */
	private void writeLocalVarDecls(List<Location<?>> locs) {
		// We start after the input and output parameters.
		for (int i = inDecls.size() + outDecls.size(); i < locs.size(); i++) {
			if (locs.get(i).getBytecode() instanceof VariableDeclaration) {
				@SuppressWarnings("unchecked")
				Location<VariableDeclaration> decl = (Location<VariableDeclaration>) locs.get(i);
				tabIndent(1);
				String name = decl.getBytecode().getName();
				out.print("var ");
				out.print(name);
				out.print(" : WVal where ");
				out.print(typePredicate(name, decl.getType()));
				out.println(";");
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

	private void writeParameters(List<Type> parameters, List<Location<?>> decls, boolean withConstraints) {
		for (int i = 0; i != parameters.size(); ++i) {
			if (i != 0) {
				out.print(", ");
			}
			VariableDeclaration locn = (VariableDeclaration) decls.get(i).getBytecode();
			String name = locn.getName();
			out.print(name + ":WVal");
			if (withConstraints) {
				out.print(" where ");
				out.print(typePredicate(name, parameters.get(i)));
			}
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
			throw new IllegalArgumentException("unknown bytecode encountered");
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
		out.print("assert toBool(");
		writeExpression(c.getOperand(0));
		out.println(");");
	}

	private void writeAssume(int indent, Location<Bytecode.Assume> c) {
		out.print("assume toBool(");
		writeExpression(c.getOperand(0));
		out.println(");");
	}

	private void writeAssign(int indent, Location<Bytecode.Assign> stmt) {
		Location<?>[] lhs = stmt.getOperandGroup(SyntaxTree.LEFTHANDSIDE);
		Location<?>[] rhs = stmt.getOperandGroup(SyntaxTree.RIGHTHANDSIDE);
		if (lhs[0].getBytecode().getOpcode() == Bytecode.OPCODE_arrayindex) {
			if (lhs.length > 1) {
				throw new IllegalArgumentException("Multiple array assignments not handled yet.");
			}
			// Instead of a[e] := v, we do a := a[e := v];
			assert lhs[0].numberOfOperands() == 2;
			Location<?> array = lhs[0].getOperand(0);
			Location<?> index = lhs[0].getOperand(1);
			writeExpression(array);
			out.print(" := fromArray(toArray(");
			writeExpression(array);
			out.print(")[toInt(");
			writeExpression(index);
			out.print(") := ");
			writeExpression(rhs[0]);
			out.print("], arraylen(");
			writeExpression(array);
			out.print("))");
		} else {
			if (isMethod(rhs[0])) {
				// Boogie distinguishes method & function calls!
				out.print("call ");
			}
			if(lhs.length > 0) {
				for(int i=0; i!=lhs.length; ++i) {
					if(i!=0) { out.print(", "); }
					writeExpression(lhs[i]);
				}
				out.print(" := ");
			}
			writeExpressions(rhs, ", ");
		}
		out.println(";");
	}

	private boolean isMethod(Location<?> loc) {
		if (loc.getBytecode().getOpcode() == Bytecode.OPCODE_invoke
				&& ((Bytecode.Invoke)loc.getBytecode()).type() instanceof Method) {
			return true;
		}
		return false;
	}

	private void writeBreak(int indent, Location<Bytecode.Break> b) {
		out.println("break;");
	}

	private void writeContinue(int indent, Location<Bytecode.Continue> b) {
		out.println("continue;");
	}

	private void writeDebug(int indent, Location<Bytecode.Debug> b) {
		// out.println("debug;");
	}

	private void writeDoWhile(int indent, Location<Bytecode.DoWhile> b) {
		Location<?>[] loopInvariant = b.getOperandGroup(0);
		// Location<?>[] modifiedOperands = b.getOperandGroup(1);
		// NOTE: Boogie does not have a do{S}while(C),
		// so we write: S;while(C){S};
		writeBlock(indent+1, b.getBlock(0));
		tabIndent(indent+1);
		out.print("while (toBool(");
		writeExpression(b.getOperand(0));
		out.print("))");
		writeLoopInvariant(indent + 2, loopInvariant);
		out.println();
		tabIndent(indent+1);
		out.println("{");
		writeBlock(indent+1, b.getBlock(0));
		tabIndent(indent+1);
		out.println("}");
	}

	private void writeFail(int indent, Location<Bytecode.Fail> c) {
		out.println("fail");
	}

	private void writeIf(int indent, Location<Bytecode.If> b) {
		out.print("if (toBool(");
		writeExpression(b.getOperand(0));
		out.println(")) {");
		writeBlock(indent+1,b.getBlock(0));
		if(b.numberOfBlocks() > 1) {
			tabIndent(indent+1);
			out.println("} else {");
			writeBlock(indent+1,b.getBlock(1));
		}
		tabIndent(indent+1);
		out.println("}");
	}

	private void writeIndirectInvoke(int indent, Location<Bytecode.IndirectInvoke> stmt) {
		Location<?>[] operands = stmt.getOperands();
		writeExpression(operands[0]);
		out.print("(");
		for(int i=1;i!=operands.length;++i) {
			if(i!=1) {
				out.print(", ");
			}
			writeExpression(operands[i]);
		}
		out.println(")");
	}

	private void writeInvoke(int indent, Location<Bytecode.Invoke> stmt) {
		out.print(stmt.getBytecode().name() + "(");
		Location<?>[] operands = stmt.getOperands();
		for(int i=0;i!=operands.length;++i) {
			if(i!=0) {
				out.print(", ");
			}
			writeExpression(operands[i]);
		}
		out.println(")");
	}

	private void writeNamedBlock(int indent, Location<Bytecode.NamedBlock> b) {
		out.print(b.getBytecode().getName());
		out.println(":");
		writeBlock(indent+1,b.getBlock(0));
	}

	private void writeWhile(int indent, Location<Bytecode.While> b) {
		Location<?>[] loopInvariant = b.getOperandGroup(0);
		// Location<?>[] modifiedOperands = b.getOperandGroup(1);
		out.print("while (toBool(");
		writeExpression(b.getOperand(0));
		out.print("))");
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
				out.print("invariant toBool(");
				writeExpression(invariant);
				out.print(");");
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
			out.print(name + " := ");
			writeExpression(operands[i]);
			out.println(";");
			tabIndent(indent+1);
		}
		out.println("return;");
	}

	private void writeSkip(int indent, Location<Bytecode.Skip> b) {
		out.println("skip;");
	}

	private void writeSwitch(int indent, Location<Bytecode.Switch> b) {
		out.print("switch ");
		writeExpression(b.getOperand(0));
		out.println(":");
		for (int i = 0; i != b.numberOfBlocks(); ++i) {
			// FIXME: ugly
			Bytecode.Case cAse = b.getBytecode().cases()[i];
			Constant[] values = cAse.values();
			tabIndent(indent + 2);
			if (values.length == 0) {
				out.println("default:");
			} else {
				out.print("case ");
				for (int j = 0; j != values.length; ++j) {
					if (j != 0) {
						out.print(", ");
					}
					out.print(values[j]);
				}
				out.println(":");
			}
			writeBlock(indent + 2, b.getBlock(i));
		}
	}

	private void writeVariableAccess(Location<VariableAccess> loc) {
		Location<VariableDeclaration> vd = getVariableDeclaration(loc.getOperand(0));
		out.print(vd.getBytecode().getName());
	}

	private void writeVariableInit(int indent, Location<VariableDeclaration> loc) {
		Location<?>[] operands = loc.getOperands();
		// out.print(loc.getType());
		// out.print(" ");
		if (operands.length > 0) {
			out.print(loc.getBytecode().getName());
			out.print(" := ");
			writeExpression(operands[0]);
			out.println(";");
		}
		// ELSE
		// TODO: Do we need a havoc here, to mimic non-det initialisation?
	}

	/**
	 * Write a bracketed operand if necessary. Any operand whose human-readable
	 * representation can contain whitespace must have brackets around it.
	 * @param operand
	 * @param enclosing
	 */
	private void writeBracketedExpression(Location<?> expr) {
		boolean needsBrackets = needsBrackets(expr.getBytecode());
		if (needsBrackets) {
			out.print("(");
		}
		writeExpression(expr);
		if (needsBrackets) {
			out.print(")");
		}
	}

	private void writeExpressions(Location<?>[] exprs, String sep) {
		for (int i = 0; i != exprs.length; ++i) {
			if (i != 0) {
				out.print(sep);
			}
			writeExpression(exprs[i]);
		}
	}

	@SuppressWarnings("unchecked")
	private void writeExpression(Location<?> expr) {
		switch (expr.getOpcode()) {
		case Bytecode.OPCODE_arraylength:
			writeArrayLength((Location<Bytecode.Operator>) expr);
			break;
		case Bytecode.OPCODE_arrayindex:
			writeArrayIndex((Location<Bytecode.Operator>) expr);
			break;
		case Bytecode.OPCODE_array:
			writeArrayInitialiser((Location<Bytecode.Operator>) expr);
			break;
		case Bytecode.OPCODE_arraygen:
			writeArrayGenerator((Location<Bytecode.Operator>) expr);
			break;
		case Bytecode.OPCODE_convert:
			writeConvert((Location<Bytecode.Convert>) expr);
			break;
		case Bytecode.OPCODE_const:
			writeConst((Location<Bytecode.Const>) expr);
			break;
		case Bytecode.OPCODE_fieldload:
			writeFieldLoad((Location<Bytecode.FieldLoad>) expr);
			break;
		case Bytecode.OPCODE_indirectinvoke:
			writeIndirectInvoke((Location<Bytecode.IndirectInvoke>) expr);
			break;
		case Bytecode.OPCODE_invoke:
			writeInvoke((Location<Bytecode.Invoke>) expr);
			break;
		case Bytecode.OPCODE_lambda:
			writeLambda((Location<Bytecode.Lambda>) expr);
			break;
		case Bytecode.OPCODE_record:
			writeRecordConstructor((Location<Bytecode.Operator>) expr, out);
			break;
		case Bytecode.OPCODE_newobject:
			writeNewObject((Location<Bytecode.Operator>) expr);
			break;
		case Bytecode.OPCODE_dereference:
			// TODO
			out.print(" TODO Bytecode.OPCODE_is ");
			break;
		case Bytecode.OPCODE_logicalnot:
			writePrefixLocations("Bool", "Bool", (Location<Bytecode.Operator>) expr);
			break;
		case Bytecode.OPCODE_neg:
			writePrefixLocations("Int", "Int", (Location<Bytecode.Operator>) expr);
			break;
		case Bytecode.OPCODE_bitwiseinvert:
			writePrefixLocations("Int", "Int", (Location<Bytecode.Operator>) expr);
			break;
		case Bytecode.OPCODE_all:
		case Bytecode.OPCODE_some:
			writeQuantifier((Location<Bytecode.Quantifier>) expr);
			break;
		case Bytecode.OPCODE_add:
		case Bytecode.OPCODE_sub:
		case Bytecode.OPCODE_mul:
		case Bytecode.OPCODE_div:
		case Bytecode.OPCODE_rem:
		case Bytecode.OPCODE_bitwiseor:  // TODO
		case Bytecode.OPCODE_bitwisexor: // TODO
		case Bytecode.OPCODE_bitwiseand: // TODO
		case Bytecode.OPCODE_shl:        // TODO
		case Bytecode.OPCODE_shr:        // TODO
			writeInfixLocations("Int", "Int", (Location<Bytecode.Operator>) expr);
			break;
		case Bytecode.OPCODE_eq:
		case Bytecode.OPCODE_ne:
		case Bytecode.OPCODE_lt:
		case Bytecode.OPCODE_le:
		case Bytecode.OPCODE_gt:
		case Bytecode.OPCODE_ge:
			writeInfixLocations("Bool", "Int", (Location<Bytecode.Operator>) expr);
			break;
		case Bytecode.OPCODE_logicaland:
		case Bytecode.OPCODE_logicalor:
			writeInfixLocations("Bool", "Bool", (Location<Bytecode.Operator>) expr);
			break;
		case Bytecode.OPCODE_is:
			// TODO: is
			out.print(" TODO Bytecode.OPCODE_is ");
			break;
		case Bytecode.OPCODE_varaccess:
			writeVariableAccess((Location<VariableAccess>) expr);
			break;
		default:
			throw new IllegalArgumentException("unknown bytecode encountered: " + expr.getBytecode());
		}
	}


	private void writeArrayLength(Location<Bytecode.Operator> expr) {
		out.print("fromInt(arraylen(");
		writeExpression(expr.getOperand(0));
		out.print("))");
	}

	private void writeArrayIndex(Location<Bytecode.Operator> expr) {
		out.print("toArray(");
		writeExpression(expr.getOperand(0));
		out.print(")[toInt(");
		writeExpression(expr.getOperand(1));
		out.print(")]");
	}

	/**
	 * Whiley array literals [a,b,c] (and strings) are represented as:
	 * <pre>
	 *   fromArray(arrayconst(null)[0 := a][1 := b][2 := c], 3)
	 * </pre>
	 *
	 * @param expr
	 */
	private void writeArrayInitialiser(Location<Bytecode.Operator> expr) {
		Location<?>[] operands = expr.getOperands();
		out.print("fromArray(arrayconst(");
		if (operands.length == 0) {
			out.print("null"); // the type of values should be irrelevant
		} else {
			writeExpression(operands[0]);
		}
		out.print(")");
		for (int i = 1; i != operands.length; ++i) {
			out.print("[" + i + " := ");
			writeExpression(operands[i]);
			out.print("]");
		}
		out.print(", ");
		out.print(operands.length);
		out.print(")");
	}

	/**
	 * Whiley array generators [val;len] are represented as:
     * <pre>
     * fromArray(arrayconst(val), len)
     * </pre>
	 * @param expr
	 */
	private void writeArrayGenerator(Location<Bytecode.Operator> expr) {
		out.print("fromArray(arrayconst(");
		writeExpression(expr.getOperand(0));
		out.print("), ");
		writeExpression(expr.getOperand(1));
		out.print(")");
	}

	private void writeConvert(Location<Bytecode.Convert> expr) {
		out.print("(" + expr.getType() + ") ");
		writeExpression(expr.getOperand(0));
	}

	private void writeConst(Location<Bytecode.Const> expr) {
		out.print(createConstant(expr.getBytecode().constant()));
	}

	private void writeFieldLoad(Location<Bytecode.FieldLoad> expr) {
		writeBracketedExpression(expr.getOperand(0));
		out.print("." + expr.getBytecode().fieldName());
	}

	private void writeIndirectInvoke(Location<Bytecode.IndirectInvoke> expr) {
		Location<?>[] operands = expr.getOperands();
		writeExpression(operands[0]);
		out.print("(");
		for(int i=1;i!=operands.length;++i) {
			if(i!=1) {
				out.print(", ");
			}
			writeExpression(operands[i]);
		}
		out.print(")");
	}

	private void writeInvoke(Location<Bytecode.Invoke> expr) {
		// TODO: check that it is safe to use unqualified DeclID names?
		out.print(expr.getBytecode().name().name() + "(");
		Location<?>[] operands = expr.getOperands();
		for(int i=0;i!=operands.length;++i) {
			if(i!=0) {
				out.print(", ");
			}
			writeExpression(operands[i]);
		}
		out.print(")");
	}

	@SuppressWarnings("unchecked")
	private void writeLambda(Location<Bytecode.Lambda> expr) {
		out.print("&[");
		Location<?>[] environment = expr.getOperandGroup(SyntaxTree.ENVIRONMENT);
		for (int i = 0; i != environment.length; ++i) {
			Location<VariableDeclaration> var = (Location<VariableDeclaration>) environment[i];
			if (i != 0) {
				out.print(", ");
			}
			out.print(var.getType());
			out.print(" ");
			out.print(var.getBytecode().getName());
		}
		out.print("](");
		Location<?>[] parameters = expr.getOperandGroup(SyntaxTree.PARAMETERS);
		for (int i = 0; i != parameters.length; ++i) {
			Location<VariableDeclaration> var = (Location<VariableDeclaration>) parameters[i];
			if (i != 0) {
				out.print(", ");
			}
			out.print(var.getType());
			out.print(" ");
			out.print(var.getBytecode().getName());
		}
		out.print(" -> ");
		writeExpression(expr.getOperand(0));
		out.print(")");
	}

	private void writeRecordConstructor(Location<Bytecode.Operator> expr, PrintWriter out) {
		Type.EffectiveRecord t = (Type.EffectiveRecord) expr.getType();
		ArrayList<String> fields = new ArrayList<String>(t.fields().keySet());
		Collections.sort(fields);
		Location<?>[] operands = expr.getOperands();
		out.print("{");
		for(int i=0;i!=operands.length;++i) {
			if(i != 0) {
				out.print(", ");
			}
			out.print(fields.get(i));
			out.print(" ");
			writeExpression(operands[i]);
		}
		out.print("}");
	}

	private void writeNewObject(Location<Bytecode.Operator> expr) {
		out.print("new ");
		writeExpression(expr.getOperand(0));
	}

	private void writePrefixLocations(String resultType, String argType, Location<Bytecode.Operator> expr) {
		// Prefix operators
		out.print("from" + resultType + "(");
		out.print(opcode(expr.getBytecode().kind()));
		out.print("to" + argType + "(");
		writeBracketedExpression(expr.getOperand(0));
		out.print("))");
	}

	private void writeInfixLocations(String resultType, String argType, Location<Bytecode.Operator> c) {
		out.print("from" + resultType + "(");
		out.print("to" + argType + "(");
		writeBracketedExpression(c.getOperand(0));
		out.print(") ");
		out.print(opcode(c.getBytecode().kind()));
		out.print(" to" + argType + "(");
		writeBracketedExpression(c.getOperand(1));
		out.print("))");
	}

	@SuppressWarnings("unchecked")
	private void writeQuantifier(Location<Bytecode.Quantifier> c) {
		out.print("fromBool(");
		final String predOp;
		switch(c.getOpcode()) {
		case Bytecode.OPCODE_some:
			out.print("(exists ");
			predOp = " && ";
			break;
		case Bytecode.OPCODE_all:
			out.print("(forall ");
			predOp = " ==> ";
			break;
		default:
			throw new IllegalArgumentException();
		}
		// first pass just declares the bound variables
		for (int i = 0; i != c.numberOfOperandGroups(); ++i) {
			Location<?>[] range = c.getOperandGroup(i);
			if (i != 0) {
				out.print(", ");
			}
			Location<VariableDeclaration>  v = (Location<VariableDeclaration>) range[SyntaxTree.VARIABLE];
			String name = v.getBytecode().getName();
			out.print(name);
			out.print(":WVal");
		}
		out.print(" :: ");
		// second pass adds the type and range constraints
		for (int i = 0; i != c.numberOfOperandGroups(); ++i) {
			Location<?>[] range = c.getOperandGroup(i);
			if (i != 0) {
				out.print(" && ");
			}
			Location<VariableDeclaration>  v = (Location<VariableDeclaration>) range[SyntaxTree.VARIABLE];
			String name = v.getBytecode().getName();
			out.print("isInt(" + name + ") && toInt(");
			writeExpression(range[SyntaxTree.START]);
			out.print(") <= toInt(" + name + ") && toInt(" + name + ") < toInt(");
			writeExpression(range[SyntaxTree.END]);
			out.print(")");
		}
		out.print(predOp);
		writeExpression(c.getOperand(SyntaxTree.CONDITION));
		out.print("))");
	}

	private boolean needsBrackets(Bytecode e) {
		switch(e.getOpcode()) {
		case Bytecode.OPCODE_convert:
		case Bytecode.OPCODE_add:
		case Bytecode.OPCODE_sub:
		case Bytecode.OPCODE_mul:
		case Bytecode.OPCODE_div:
		case Bytecode.OPCODE_rem:
		case Bytecode.OPCODE_eq:
		case Bytecode.OPCODE_ne:
		case Bytecode.OPCODE_lt:
		case Bytecode.OPCODE_le:
		case Bytecode.OPCODE_gt:
		case Bytecode.OPCODE_ge:
		case Bytecode.OPCODE_logicaland:
		case Bytecode.OPCODE_logicalor:
		case Bytecode.OPCODE_bitwiseor:
		case Bytecode.OPCODE_bitwisexor:
		case Bytecode.OPCODE_bitwiseand:
		case Bytecode.OPCODE_shl:
		case Bytecode.OPCODE_shr:
		case Bytecode.OPCODE_is:
		case Bytecode.OPCODE_newobject:
		case Bytecode.OPCODE_dereference:
			return true;
		}
		return false;
	}

	private static String opcode(Bytecode.OperatorKind k) {
		switch(k) {
		case NEG:
			return "-";
		case NOT:
			return "!";
		case BITWISEINVERT:
			return "~";
		case DEREFERENCE:
			return "*";
		// Binary
		case ADD:
			return "+";
		case SUB:
			return "-";
		case MUL:
			return "*";
		case DIV:
			return "/";
		case REM:
			return "%";
		case EQ:
			return "==";
		case NEQ:
			return "!=";
		case LT:
			return "<";
		case LTEQ:
			return "<=";
		case GT:
			return ">";
		case GTEQ:
			return ">=";
		case AND:
			return "&&";
		case OR:
			return "||";
		case BITWISEOR:
			return "|";
		case BITWISEXOR:
			return "^";
		case BITWISEAND:
			return "&";
		case LEFTSHIFT:
			return "<<";
		case RIGHTSHIFT:
			return ">>";
		case IS:
			return "is";
		case NEW:
			return "new";
		default:
			throw new IllegalArgumentException("unknown operator kind : " + k);
		}
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
	 * @param var the name of the variable being typed.
	 * @param type the WyIL type
	 * @return a Boogie typing predicate, such as "isInt(a)".
	 */
	public String typePredicate(String var, Type type) {
		if (type instanceof Type.Nominal) {
			String typeName = ((Type.Nominal) type).name().name();
			return typePredicateName(typeName) + "(" + var + ")";
		}
		if (type instanceof Type.Int) {
			return "isInt(" + var + ")";
		}
		if (type instanceof Type.Array) {
			return "isArray(" + var + ")";
			// TODO: add constraints on the element type
			//translateType(var, ((Type.Array) type).element(), stores);
		}
//		if (type instanceof Type.Void) {
//			// this should not happen?
//			return "TODO Type.Void";
//		}
		if (type instanceof Type.Record) {
			// TODO: add constraints about the fields?
			// HashMap<String, Type> fields = ((Type.Record) type).fields();
			if (((Type.Record) type).isOpen()) {
				return "isObject(" + var + ")";
			} else {
				return "isRecord(" + var + ")";
			}
//			// Check if the field is the function call of print,...
//			if (fields.containsKey("print") || fields.containsKey("println") || fields.containsKey("print_s")
//					|| fields.containsKey("println_s")) {
//				// No need to do the translation.
//				return "void*";
//			}
//
//			// The input 'type' is input arguments of main method.
//			if (fields.containsKey("args")) {
//				return "int argc, char** args";
//			}
//			// Get the user-defined type
//			return Optional.ofNullable(stores.getUserDefinedType(type)).get().name() + "*";
		}
		if (type instanceof Type.Union) {
			// Type.Union u = (Type.Union) type;
			// TODO: generate the disjunction of all the bounds??
			// u.bounds()
			// return Optional.ofNullable(stores.getUserDefinedType(type)).get().name() + "*";
		}
		if (type instanceof Type.Reference) {
			// TODO: add constraints about the type pointed to?
			// Type.Reference ref = (Type.Reference) type;
			// translateType(?, ref.element(), stores);
			return "isRef(" + var + ")";
		}
		if (type instanceof Type.Function) {
			// TODO: add input and output types?
			return "isFunc(" + var + ")";
		}
		if (type instanceof Type.Method) {
			// TODO: add input and output types?
			return "isMethod(" + var + ")";
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
		throw new RuntimeException("TODO: type " + type);
	}

	/**
	 * Create a type predicate name, like "isList", from a type name "list".
	 *
	 * @param typeName a non-empty string.
	 * @return a non-null string.
	 */
	private String typePredicateName(String typeName) {
		return "is" + typeName.substring(0, 1).toUpperCase() + typeName.substring(1);
	}

	/**
	 * Given a constant of the given type, cast it into a WVal value.
	 *
	 * @param cd a Whiley constant, with a type.
	 * @return an expression string with type WVal.
	 */
	private String createConstant(Constant cd) {
		Type type = cd.type();
		if (cd instanceof Constant.Integer) {
			return "fromInt(" + cd.toString() + ")";
		}
		if (cd instanceof Constant.Bool) {
			return "fromBool(" + cd.toString() + ")";
		}
		if (cd instanceof Constant.Byte) {
			return "fromInt(" + cd.toString() + ")";
		}
		if (cd instanceof Constant.Array) {
			Constant.Array aconst = (Constant.Array) cd;
			ArrayList<Constant> values = aconst.values();
			return createArrayInitialiser(values);
		}
		if (cd instanceof Constant.Null) {
			return "null"; // already a WVal
		}
		throw new RuntimeException("TODO: constantToWVal(" + cd + "):" + type);
	}

	private String createArrayInitialiser(ArrayList<Constant> values) {
		StringBuilder out = new StringBuilder();
		out.append("fromArray(arrayconst(");
		if (values.size() == 0) {
			out.append("null"); // the type of values should be irrelevant
		} else {
			out.append(createConstant(values.get(0)));
		}
		out.append(")");
		for (int i = 1; i != values.size(); ++i) {
			out.append("[" + i + " := ");
			out.append(createConstant(values.get(i)));
			out.append("]");
		}
		out.append(", ");
		out.append(values.size());
		out.append(")");
		return out.toString();
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
		if (path.endsWith(".whiley")) {
			System.out.println("compiling " + path);
			Pair<Integer,String> ok = compile(path);
			if (ok.first() != 0) {
				System.err.println("Error compiling " + path);
				System.err.println(ok.second());
				System.exit(2);
			}
			path = path.replaceAll("\\.whiley", ".wyil");
			System.out.println("path set to " + path);
		}
		if (path.endsWith(".wyil")) {
			String bplPath = path.substring(0, path.length() - 5) + ".bpl";
			System.out.println("loading " + path);
			try {
				PrintWriter out = new PrintWriter(new File(bplPath));
				FileInputStream fin = new FileInputStream(path);
				WyilFile wf = new WyilFileReader(fin).read();
				Wyil2Boogie translator = new Wyil2Boogie(out);
				translator.setVerbose(verbose);
				translator.apply(wf);
			} catch (InternalFailure e) {
				e.outputSourceError(System.err);
			} catch (SyntaxError e) {
				e.outputSourceError(System.err);
			}
		} else {
			System.err.println("Unknown file: " + path);
			System.exit(3);
		}
	}

}
