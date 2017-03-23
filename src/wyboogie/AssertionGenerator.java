package wyboogie;

import static wyboogie.BoogieType.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import wyil.lang.Bytecode;
import wyil.lang.SyntaxTree;
import wyil.lang.Type;
import wyil.lang.Bytecode.VariableAccess;
import wyil.lang.Bytecode.VariableDeclaration;
import wyil.lang.SyntaxTree.Location;

/**
 * Generate assertions to ensure that a given expression is well-defined.
 *
 * @author Mark Utting
 *
 */
public class AssertionGenerator {
    private final Wyil2Boogie wy2b;

    protected final BoogieExpr ZERO = new BoogieExpr(INT, "0");

    private int currentIndent;

    /** All the conjuncts that we can assume for the current verification condition. */
    private List<String> bndVars = new ArrayList<>();

    /** All the bound vars that we need to universally quantify over. */
    private List<BoogieExpr> context = new ArrayList<>();

    public AssertionGenerator(Wyil2Boogie wyil2Boogie) {
        wy2b = wyil2Boogie;
    }

    /**
     * Check expr in the context of a universally quantifier variable, var.
     *
     * @param var
     * @param expr
     */
    private void declareAndCheck(List<String> vars, List<BoogieExpr> conjuncts, Location<?> expr) {
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
     * @param conjunct
     * @param expr
     */
    private void assumeAndCheck(List<BoogieExpr> conjuncts, Location<?> expr) {
        int size = context.size();
        context.addAll(conjuncts);
        check(expr);
        while (context.size() > size) {
            context.remove(context.size() - 1);
        }
    }

    /** Translate a Whiley expression into a Boogie expression. */
    protected BoogieExpr expr(Location<?> expr) {
        return wy2b.expr(expr);
    }

    /**
     * Generate a Boogie assertion to check the given conjecture.
     *
     * @param conjecture
     */
    protected void generateCheck(BoogieExpr conjecture) {
        wy2b.generateAssertion(currentIndent, bndVars, context, conjecture);
    }

    /**
     * Main entry point for this assertion generator.
     *
     * @param indent indentation of the current assertion line.
     *              (assumes that this indentation has already been added, but
     *              similar or greater indentation will be added for subsequent lines).
     * @param expr a predicate/expression to check for well-definedness.
     */
    public void checkPredicate(int indent, Location<?> expr) {
        context.clear();
        currentIndent = indent;
        check(expr);
        assert context.size() == 0;
    }

    /**
     * Convenience entry point to check a whole array of expressions.
     *
     * @param indent
     * @param exprs an array of predicates/expressions to check for well-definedness.
     */
    public void checkPredicates(int indent, Location<?>[] exprs) {
        for (Location<?> loc : exprs) {
            checkPredicate(indent, loc);
        }
    }

    /**
     * A recursive helper for checkPredicate.
     *
     * This descends into sub-expressions, and records useful context information.
     */
    private void check(Location<?> expr) {
        // The default is that after this switch, we still check all subexpressions.
        // If a case has already checked all subexpressions, it should return, not break.
        switch (expr.getOpcode()) {

        case Bytecode.OPCODE_arrayindex:
            // check that 0 <= index < arraylen(array).
            BoogieExpr indexInBounds = new BoogieExpr(BOOL);
            BoogieExpr array = expr(expr.getOperand(0)).asWVal();
            BoogieExpr arraylen = new BoogieExpr(INT, "arraylen(" + array.toString() + ")");
            BoogieExpr index = expr(expr.getOperand(1)).as(INT);
            indexInBounds.addOp(ZERO, " <= ", index);
            indexInBounds.addOp(" && ", new BoogieExpr(BOOL, index, " < ", arraylen));
            assert indexInBounds.getOp().equals(" && ");
            generateCheck(indexInBounds);
            break;

//        case Bytecode.OPCODE_arraygen:
//            // check that: 0 <= length.
//            return writeArrayGenerator((Location<Bytecode.Operator>) expr);
//
//        case Bytecode.OPCODE_indirectinvoke:
//            return writeIndirectInvoke((Location<Bytecode.IndirectInvoke>) expr);

        case Bytecode.OPCODE_invoke:
            Bytecode.Invoke funCall = (Bytecode.Invoke) expr.getBytecode();
            String name = funCall.name().name();
            Type.FunctionOrMethod type = funCall.type();
            String funName = wy2b.mangleFunctionMethodName(name, type);
            Location<?>[] operands = expr.getOperands();
            BoogieExpr funPre = new BoogieExpr(BOOL, funName + Wyil2Boogie.METHOD_PRE + "(");
            for(int i=0;i!=operands.length;++i) {
                if(i!=0) {
                    funPre.print(", ");
                }
                funPre.addExpr(expr(operands[i]).asWVal());
            }
            funPre.print(")");
            generateCheck(funPre);
            break;  // continue checking all subexpressions too.

//        case Bytecode.OPCODE_lambda:
//            return writeLambda((Location<Bytecode.Lambda>) expr);
//
//        case Bytecode.OPCODE_record:
//            BoogieExpr[] rvals = Arrays.stream(expr.getOperands()).map(this::expr).toArray(BoogieExpr[]::new);
//            return createRecordConstructor((Type.EffectiveRecord) expr.getType(), rvals);
//
//        case Bytecode.OPCODE_newobject:
//            return writeNewObject((Location<Bytecode.Operator>) expr);
//
//        case Bytecode.OPCODE_dereference:
//            // TODO: dereference
//            throw new NotImplementedYet("dereference", expr);
//
//        case Bytecode.OPCODE_neg:
//            return prefixOp(INT, expr, "- ", INT);

        case Bytecode.OPCODE_all:
            List<String> vars = new ArrayList<>();
            List<BoogieExpr> constraints = new ArrayList<>();
            for (int i = 0; i != expr.numberOfOperandGroups(); i++) {
                Location<?>[] range = expr.getOperandGroup(i);
                // declare the bound variable: v:WVal
                @SuppressWarnings("unchecked")
                Location<VariableDeclaration>  v = (Location<VariableDeclaration>) range[SyntaxTree.VARIABLE];
                String bndName = v.getBytecode().getName();
                vars.add(bndName);

                // and add the constraint: isInt(v) && start <= v && v <= end
                BoogieExpr vExpr = new BoogieExpr(WVAL, bndName).as(INT);
                Location<?> low = range[SyntaxTree.START];
                Location<?> high = range[SyntaxTree.END];
                check(low);
                check(high);
                BoogieExpr lowExpr = expr(low).as(INT);
                BoogieExpr highExpr = expr(high).as(INT);
                constraints.add(new BoogieExpr(BOOL, "isInt(" + bndName + ")"));
                constraints.add(new BoogieExpr(BOOL, lowExpr, " <= ", vExpr));
                constraints.add(new BoogieExpr(BOOL, vExpr, " < ", highExpr));
            }
            declareAndCheck(vars, constraints, expr.getOperand(SyntaxTree.CONDITION));
            return; // we have checked all sub-expressions

//        case Bytecode.OPCODE_some:
//            return writeQuantifier("exists", " && ", (Location<Bytecode.Quantifier>) expr);

        case Bytecode.OPCODE_div:
        case Bytecode.OPCODE_rem:
            // check constraint: rhs != 0
            BoogieExpr rhs = expr(expr.getOperand(1)).as(INT).withBrackets(" != ");
            BoogieExpr rhsNonZero = new BoogieExpr(BOOL, rhs.toString() + " != 0");
            generateCheck(rhsNonZero);
            break;  // carry on checking subexpressions.

//        case Bytecode.OPCODE_logicalnot:
              // TODO: does this upset our context calculations?
//            return prefixOp(BOOL, expr, "! ", BOOL);

        case Bytecode.OPCODE_logicaland:
            check(expr.getOperand(0));
            // assume the LHS while checking the RHS.
            BoogieExpr lhsAnd = expr(expr.getOperand(0)).as(BOOL);
            assumeAndCheck(Collections.singletonList(lhsAnd), expr.getOperand(1));
            return;

        case Bytecode.OPCODE_logicalor:
            check(expr.getOperand(0));
            // assume the negation of the LHS while checking the RHS.
            BoogieExpr lhsOr = expr(expr.getOperand(0)).as(BOOL);
            BoogieExpr negLhs = new BoogieExpr(BOOL);
            negLhs.addOp("! ", lhsOr);
            assert negLhs.getOp().equals("! ");
            assumeAndCheck(Collections.singletonList(negLhs), expr.getOperand(1));
            return;

        case Bytecode.OPCODE_varaccess:
            return; // we must NOT go back to the declaration, since we've already checked that earlier.

        }
        // The default behaviour is to check all sub-expressions.
        // System.out.println("  looping thru " + expr.numberOfOperands() + " args of " + expr);
        for (Location<?> loc : expr.getOperands()) {
            check(loc);
        }
    }



}
