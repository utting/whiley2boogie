/**
 *
 */
package wyboogie;

import java.util.HashSet;
import java.util.Set;

/**
 * Stores the textual representation of one Boogie term.
 *
 * This includes the string form of the term,
 * plus some knowledge about the type of the term and its precedence.
 * Type coercions are added lazily, when needed (see the 'as' and 'asWVal' functions).
 *
 * The expression tries to keep track of the weakest Boogie operator that has been added
 * inside the expression, so that brackets can be added only when necessary.
 * However, if you build expressions with brackets, or complex arrangements of operators,
 * you should call setOp(outer) manually at the end to ensure that the expression has the
 * correct (weakest) outer operator.
 *
 * The precedence of the outermost operator (as returned by getOp()) ranges from the
 * Boogie equivalence operator up to the array index operator.  So it is always safe
 * to separate these BoogieExpr objects with commas.
 *
 *
 * @author Mark Utting
 */
public class BoogieExpr {

    private final StringBuilder builder = new StringBuilder();
    private BoogieType termType;

    // the outermost Boogie operator of this expression.  null means the expression is atomic.
    private String outermostOp = null;

    private static final Set<String> assocOps = new HashSet<String>();
    static {
        assocOps.add(" || ");
        assocOps.add(" && ");
        assocOps.add(" ++ ");
        assocOps.add(" + ");
        assocOps.add(" * ");
    }

    /**
     * Create an atomic Boogie term whose type is BoogieType.WVAL.
     */
    public BoogieExpr() {
        termType = BoogieType.WVAL;
    }

    /**
     * Create an atomic Boogie term of the given type.
     */
    public BoogieExpr(BoogieType type) {
        termType = type;
    }

    /**
     * Create an atomic Boogie term of the given type, containing the given string.
     */
    public BoogieExpr(BoogieType type, String str) {
        termType = type;
        builder.append(str);
    }

    /**
     * Create a Boogie term for an infix operator plus its arguments.
     */
    public BoogieExpr(BoogieType type, BoogieExpr lhs, String op, BoogieExpr rhs) {
        termType = type;
        addOp(lhs, op, rhs);
    }

    /**
     *
     * @return the type of this whole expression.
     */
    public BoogieType getType() {
        return termType;
    }

    /**
     * True if this expression is atomic (has no outermost operator).
     * For example, constants and fully bracketed expressions are atomic.
     *
     * @return
     */
    public boolean isAtomic() {
        return outermostOp == null;
    }

    /**
     * @return the outermost operator of this expression, or null if it is atomic.
     */
    public String getOp() {
        return outermostOp;
    }

    /**
     * Set the outermost operator of this expression.
     * @param a known Boogie operator, or null if this expression is atomic.
     */
    public void setOp(String op) {
        if (op != null) {
            boogiePrecedence(op);  // will throw exception if operator is unknown.
        }
        outermostOp = op;
    }

    /**
     * This is similar to setOp, but is conditional.
     *
     * If expr has a weaker-binding outermost operator than this expression,
     * its operator is adopted as the outermost operator of this expression.
     *
     * This is an approximate heuristic, since some Boogie operators have the same
     * precedence level.  In this case, we retain the FIRST of the weakest operators seen.
     * This is why clients who construct complex expressions should call setOp manually.
     *
     * @param expr a known Boogie operator, or null.
     */
    public void setOpIfWeaker(String op) {
        if (outermostOp == null
            || op != null && boogiePrecedence(op) < boogiePrecedence(outermostOp)) {
            setOp(op);
        }
    }

    /**
     * Append the given string to this expression.
     *
     * @param str
     */
    public void append(String str) {
        builder.append(str);
    }

    public void appendf(String format, Object... args) {
        builder.append(String.format(format, args));
    }

    @Override
    public String toString() {
        return builder.toString();
    }

    /**
     * Coerce the term to a WVal string.
     * @return
     */
    public BoogieExpr asWVal() {
        if (termType == BoogieType.WVAL) {
            return this;
        } else {
            BoogieExpr result = new BoogieExpr(BoogieType.WVAL);
            result.append("from");
            result.append(termType.toString());
            result.append("(");
            result.builder.append(this.builder);
            result.append(")");
            return result;
        }
    }

    /**
     * Coerce the term down to the requested subtype.
     *
     * @param type Must be a strict subtype of WVal.
     * @return
     */
    public BoogieExpr as(BoogieType type) {
        assert type != BoogieType.WVAL;
        if (termType == type) {
            return this;
        } else if (termType == BoogieType.WVAL){
            BoogieExpr result = new BoogieExpr(type);
            result.append("to");
            result.append(type.toString());
            result.append("(");
            result.builder.append(this.builder.toString());
            result.append(")");
            return result;
        } else {
            throw new IllegalArgumentException("Cannot coerce " + builder.toString() + " to " + type);
        }
    }

    /**
     * Adds expr to this term, with brackets around it if necessary.
     * Note that op is not added to the term, it is just to decide if brackets are necessary.
     *
     * @param expr
     * @param op
     */
    public void addAndBracketExpr(BoogieExpr expr, String op) {
        if (expr.needsBrackets(op)) {
            builder.append("(");
            builder.append(expr.builder);
            builder.append(")");
        } else {
            builder.append(expr.builder);
        }
    }

    /**
     * Adds expr to this term, without any bracket checking.
     * This automatically calls <pre>setOpIfWeaker(expr.getOp())</pre>.
     *
     * @param expr
     */
    public void addExpr(BoogieExpr expr) {
        builder.append(expr.builder);
        setOpIfWeaker(expr.outermostOp);
    }

    /**
     * See if this expression needs parentheses.
     *
     * @param op a known Boogie operator
     * @return true if this expression needs parentheses before applying op to it.
     */
    public boolean needsBrackets(String op) {
        if (outermostOp == null) {
            return false;
        }
        int opPrec = boogiePrecedence(op);
        int thisPrec = boogiePrecedence(outermostOp);
        if (thisPrec > opPrec) {
            // this expr has a tighter-binding operator than op, so no brackets needed.
            return false;
        }
        if (op.equals(outermostOp)) {
            // needs brackets, unless it is a safe associative operator.
            return !isAssociative(op);
        }
        return true;
    }

    public static int boogiePrecedence(String op) {
        switch (op) {
        case " <==> ": return 0;

        case " ==> ": return 1;

        case " || ":
        case " && ": return 2;

        case " == ":
        case " != ":
        case " < ":
        case " <= ":
        case " > ":
        case " >= ":
        case " <: ": return 3;

        case " ++ ": return 4;

        case " + ":
        case " - ": return 5;

        case " * ":
        case " / ":
        case " % ":
        case " div ":
        case " mod ": return 6;

        // unary operators
        case "- ":
        case "! ": return 7;

        case "[": return 8;

        default: throw new IllegalArgumentException("Unknown Boogie operator " + op);
        }
    }

    public static boolean isAssociative(String op) {
        return assocOps.contains(op);
    }

    /**
     * Add a prefix operator (or a repeated infix operator).
     * This automatically calls <pre>setOpIfWeaker(op)</pre>.
     *
     * @param op a prefix (must have a trailing space) or infix (must have leading and trailing space) Boogie operator.
     * @param rhs the right hand side expression, printed after the operator.
     */
    public void addOp(String op, BoogieExpr rhs) {
        builder.append(op);
        addAndBracketExpr(rhs, op);
        setOpIfWeaker(op);
    }

    /**
     * Add an infix operator.
     * This automatically calls <pre>setOpIfWeaker(op)</pre>.
     *
     * @param lhs the left hand side expression, printed before the operator.
     * @param op an infix Boogie operator.  Must have a leading and trailing space.
     * @param rhs the right hand side expression, printed after the operator.
     */
    public void addOp(BoogieExpr lhs, String op, BoogieExpr rhs) {
        addAndBracketExpr(lhs, op);
        builder.append(op);
        addAndBracketExpr(rhs, op);
        setOpIfWeaker(op);
    }

    /**
     * Wraps this expression in parentheses (if necessary) to ensure that it is an atomic expression.
     *
     * @return a BoogieExpr whose outermost operator is null.
     */
    public BoogieExpr asAtom() {
        if (outermostOp == null) {
            return this;
        } else {
            return new BoogieExpr(termType, "(" + this.toString() + ")");
        }
    }

    /**
     * Returns this expression, but with brackets added around it if necessary.
     * @param op the context where this expression will be used.
     * @return a safe expression for that context.
     */
    public BoogieExpr withBrackets(String op) {
        if (needsBrackets(op)) {
            BoogieExpr result = new BoogieExpr(this.termType);
            result.addAndBracketExpr(this, op);
            return result;
        } else {
            return this;
        }
    }
}
