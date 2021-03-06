package wy2boogie.translate;

import static wy2boogie.translate.BoogieType.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import wybs.lang.Build;
import wyil.util.AbstractVisitor;

import static wyil.lang.WyilFile.*;

/**
 * Generate assertions to ensure that a given expression is well-defined.
 *
 * Note that checks are generated in bottom-up order so that sub-expressions are checked
 * before the outer expressions.  This allows assumptions about the sub-expression results
 * to help with the proofs of the whole expression.
 *
 * @author Mark Utting
 *
 */
public class AssertionGenerator {
	private final Build.Meter meter;
    private final Wyil2Boogie wy2b;

    private final BoogieExpr ZERO = new BoogieExpr(INT, "0");

    private int currentIndent;

    /** All the conjuncts that we can assume for the current verification condition. */
    private List<String> bndVars = new ArrayList<>();

    /** All the bound vars that we need to universally quantify over. */
    private List<BoogieExpr> context = new ArrayList<>();
	private String currentFunctionMethodName;

	public AssertionGenerator(Build.Meter meter, Wyil2Boogie wyil2Boogie) {
		this.meter = meter;
        this.wy2b = wyil2Boogie;
    }

    /**
     * Check expr isType the context of a universally quantifier variable, var.
     *
     * @param vars bound variables
     * @param conjuncts constraints on the bound variables
     * @param expr the main body of the quantifier
     */
    private void declareAndCheck(List<String> vars, List<BoogieExpr> conjuncts, Expr expr) {
        int size = bndVars.size();
        bndVars.addAll(vars);
        assumeAndCheck(conjuncts, expr);
        while (bndVars.size() > size) {
            bndVars.remove(bndVars.size() - 1);
        }
    }

    /**
     * Check expr under the assumption of conjunct.
     *
     * @param conjuncts predicates that can be assumed true during the checking of expr.
     * @param expr the expression to check.
     */
    private void assumeAndCheck(List<BoogieExpr> conjuncts, Expr expr) {
        int size = context.size();
        context.addAll(conjuncts);
        check(expr);
        while (context.size() > size) {
            context.remove(context.size() - 1);
        }
    }

    /** Translate a Whiley expression into a Boogie expression. */
    private BoogieExpr expr(Expr expr) {
        return wy2b.writeAllocations(0, expr);
    }

    /**
     * Generate a Boogie assertion to check the given conjecture.
     *
     * @param conjecture the predicate to check.
     */
    private void generateCheck(BoogieExpr conjecture) {
        wy2b.generateAssertion(currentIndent, "assert", bndVars, context, conjecture);
    }

	/**
	 * Generate a Boogie assertion to check the given conjecture.
	 *
	 * @param conjecture the predicate to check.
	 */
	private void generateAssume(BoogieExpr conjecture) {
		wy2b.generateAssertion(currentIndent, "assume", bndVars, context, conjecture);
	}

    /**
     * Main entry point for this assertion generator.
     *
     * @param indent indentation of the current assertion line.
     *              (assumes that this indentation has already been added, but
     *              similar or greater indentation will be added for subsequent lines).
     * @param expr a predicate/expression to check for well-definedness.
     */
    public void checkPredicate(int indent, Expr expr) {
        context.clear();
        currentIndent = indent;
        check(expr);
        assert context.size() == 0;
    }

    /**
     * Convenience entry point to check a whole array of expressions.
     *
     * @param indent how many levels to indent this whole assertion.
     * @param exprs an array of predicates/expressions to check for well-definedness.
     */
    public void checkPredicates(int indent, Tuple<? extends Expr> exprs) {
        for (Expr loc : exprs) {
            checkPredicate(indent, loc);
        }
    }

    /**
     * A recursive helper for checkPredicate.
     *
     * This descends into sub-expressions, and records useful context information.
     */
    private void check(Expr expr) {
    	final Wyil2Boogie this_wy2b = this.wy2b;
		AbstractVisitor visitor = new AbstractVisitor(meter) {

			@Override
			public void visitArrayAccess(Expr.ArrayAccess expr) {
				// first check all subexpressions, to ensure they are valid.
				super.visitArrayAccess(expr);

				// check that 0 <= index < arraylen(array).
				BoogieExpr indexInBounds = new BoogieExpr(BOOL);
				BoogieExpr array = expr(expr.getFirstOperand()).asWVal();
				BoogieExpr arraylen = new BoogieExpr(INT, "arraylen(" + array.toString() + ")");
				BoogieExpr index = expr(expr.getSecondOperand()).as(INT);
				indexInBounds.addOp(ZERO, " <= ", index);
				indexInBounds.addOp(" && ", new BoogieExpr(BOOL, index, " < ", arraylen));
				assert indexInBounds.getOp().equals(" && ");
				generateCheck(indexInBounds);
			}

			// case Bytecode.OPCODE_arraygen:
			// TODO: check that: 0 <= length.
			// return writeArrayGenerator((Location<Bytecode.Operator>) expr);
			//
			// case Bytecode.OPCODE_indirectinvoke:
			// TODO: can we generate any useful checks for this, without knowing the function?
			// return writeIndirectInvoke((Location<Bytecode.IndirectInvoke>) expr);


			@Override
			public void visitLambda(Decl.Lambda decl) {
				// do not recurse inside lambda functions, since their input is unknown at this point.
			}

			@Override
			public void visitInvoke(Expr.Invoke funCall) {
				// First check all subexpressions
				super.visitInvoke(funCall);

				QualifiedName name = funCall.getBinding().getDeclaration().getQualifiedName();
				Type.Callable type = funCall.getBinding().getDeclaration().getType();
				// Now check any preconditions.
				//
				// NOTE that this applies only to simple functions, because properties do not have preconditions,
				// and methods (plus complex functions with multiple results!) use the Boogie 'call' mechanism,
				// which already checks preconditions and assumes the postconditions.
				// So it is just the simple functions that we need to check preconditions and assume their
				// postconditions here. (An alternative approach is to use global axioms to define the
				// pre-post effects of functions, but this requires those axioms to be guarded so that
				// they cannot be used while the body of the function itself is being verified).
				if ((type instanceof Type.Function) && !this_wy2b.callAsProcedure(funCall)) {
					// Now check the precondition of this function.
					String funName = wy2b.getMangledFunctionMethodName(name, type);
					Tuple<Expr> operands = funCall.getOperands();
					String args = wy2b.commaSep(wy2b.typeParamValuesString(funCall), getArgs(operands));
					String call = funName + "(" + args + ")";
					String pre = funName + Wyil2Boogie.METHOD_PRE + "(" + args + ")";
					String post = funName + Wyil2Boogie.METHOD_POST + "(" + wy2b.commaSep(args, call) + ")";
					BoogieExpr funPre = new BoogieExpr(BOOL, pre);
					BoogieExpr funPost = new BoogieExpr(BOOL, post);
					generateCheck(funPre);
					// assume the functions postcondition, unless we are part of a recursive cycle with it.
					if (type instanceof Type.Function &&
							!wy2b.canRecurseBackTo(funName, getCurrentFunctionMethodName())) {
						generateAssume(funPost);
					}
				}
			}

			private String getArgs(Tuple<Expr> operands) {
				return wy2b.commaSepMap(operands, e -> expr(e).asWVal().toString());
			}

			// case Bytecode.OPCODE_record:
			// BoogieExpr[] rvals =
			// Arrays.stream(expr.getOperands()).map(this::expr).toArray(BoogieExpr[]::new);
			// return createRecordConstructor((Type.EffectiveRecord) expr.getType(), rvals);
			//
			// case Bytecode.OPCODE_newobject:
			// return writeNewObject((Location<Bytecode.Operator>) expr);
			//
			// case Bytecode.OPCODE_dereference:
			// // TODO: dereference
			// throw new NotImplementedYet("dereference", expr);
			//
			// case Bytecode.OPCODE_neg:
			// return prefixOp(INT, expr, "- ", INT);

			@Override
			public void visitUniversalQuantifier(Expr.UniversalQuantifier expr) {
				List<String> vars = new ArrayList<>();
				List<BoogieExpr> constraints = new ArrayList<>();
				for (Decl.StaticVariable parameter : expr.getParameters()) {
					Expr.ArrayRange range = (Expr.ArrayRange) parameter.getInitialiser();
					// declare the bound variable: v:WVal
					String bndName = parameter.getName().get();
					vars.add(bndName);

					// and add the constraint: isInt(v) && start <= v && v <= end
					BoogieExpr vExpr = new BoogieExpr(WVAL, bndName).as(INT);
					Expr low = range.getFirstOperand();
					Expr high = range.getSecondOperand();
					check(low);
					check(high);
					BoogieExpr lowExpr = expr(low).as(INT);
					BoogieExpr highExpr = expr(high).as(INT);
					constraints.add(new BoogieExpr(BOOL, "isInt(" + bndName + ")"));
					constraints.add(new BoogieExpr(BOOL, lowExpr, " <= ", vExpr));
					constraints.add(new BoogieExpr(BOOL, vExpr, " < ", highExpr));
				}
				declareAndCheck(vars, constraints, expr.getOperand());
			}

			@Override
			public void visitExistentialQuantifier(Expr.ExistentialQuantifier expr) {
				// do not go inside because correctness checks inside it usually depend upon the existential vars.
			}

			@Override
			public void visitIntegerDivision(Expr.IntegerDivision expr) {
				// First check subexpressions
				super.visitIntegerDivision(expr);

				// check constraint: rhs != 0
				BoogieExpr rhs = expr(expr.getSecondOperand()).as(INT).withBrackets(" != ");
				BoogieExpr rhsNonZero = new BoogieExpr(BOOL, rhs.toString() + " != 0");
				generateCheck(rhsNonZero);
			}

			@Override
			public void visitIntegerRemainder(Expr.IntegerRemainder expr) {
				// First check subexpressions
				super.visitIntegerRemainder(expr);

				// check constraint: rhs != 0
				BoogieExpr rhs = expr(expr.getSecondOperand()).as(INT).withBrackets(" != ");
				BoogieExpr rhsNonZero = new BoogieExpr(BOOL, rhs.toString() + " != 0");
				generateCheck(rhsNonZero);
			}

			// case Bytecode.OPCODE_logicalnot:
			// TODO: does this upset our context calculations?
			// return prefixOp(BOOL, expr, "! ", BOOL);

			@Override
			public void visitLogicalAnd(Expr.LogicalAnd expr) {
				Tuple<Expr> operands = expr.getOperands();
				check(operands.get(0));
				// assume the LHS while checking the RHS.
				BoogieExpr lhsAnd = expr(operands.get(0)).as(BOOL);
				assumeAndCheck(Collections.singletonList(lhsAnd), operands.get(1));
			}

			@Override
			public void visitLogicalOr(Expr.LogicalOr expr) {
				Tuple<Expr> operands = expr.getOperands();
				check(operands.get(0));
				// assume the negation of the LHS while checking the RHS.
				BoogieExpr lhsOr = expr(operands.get(0)).as(BOOL);
				BoogieExpr negLhs = new BoogieExpr(BOOL);
				negLhs.addOp("! ", lhsOr);
				assert negLhs.getOp().equals("! ");
				assumeAndCheck(Collections.singletonList(negLhs), operands.get(1));
			}

			@Override
			public void visitLogicalImplication(Expr.LogicalImplication expr) {
				check(expr.getFirstOperand());
				// assume the LHS while checking the RHS.
				BoogieExpr lhsOr = expr(expr.getFirstOperand()).as(BOOL);
				assumeAndCheck(Collections.singletonList(lhsOr), expr.getSecondOperand());
			}
		};
        // The default behaviour is to check all sub-expressions.
        visitor.visitExpression(expr);
    }

	public void setCurrentFunctionMethodName(String currentFunctionMethodName) {
		this.currentFunctionMethodName = currentFunctionMethodName;
	}

	public String getCurrentFunctionMethodName() {
		return currentFunctionMethodName;
	}
}
