/**
 *
 */
package wy2boogie.translate;

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
    private final BoogieType termType;

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
        this.termType = BoogieType.WVAL;
    }

    /**
     * Create an atomic Boogie term of the given type.
     */
    public BoogieExpr(BoogieType type) {
        this.termType = type;
    }

    /**
     * Create an atomic Boogie term of the given type, containing the given string.
     */
    public BoogieExpr(BoogieType type, String str) {
        this.termType = type;
        this.builder.append(str);
    }

    /**
     * Create a Boogie term for an infix operator plus its arguments.
     */
    public BoogieExpr(BoogieType type, BoogieExpr lhs, String op, BoogieExpr rhs) {
        this.termType = type;
        addOp(lhs, op, rhs);
    }

    /**
     *
     * @return the type of this whole expression.
     */
    public BoogieType getType() {
        return this.termType;
    }

    /**
     * See if this expression is atomic.
     * For example, constants and fully bracketed expressions are atomic.
     *
     * @return true if this expression is atomic (has no outermost operator)
     */
    public boolean isAtomic() {
        return this.outermostOp == null;
    }

    /**
     * @return the outermost operator of this expression, or null if it is atomic.
     */
    public String getOp() {
        return this.outermostOp;
    }

    /**
     * Set the outermost operator of this expression.
     *
     * @param op a known Boogie operator, or null if this expression is atomic.
     */
    public void setOp(String op) {
        if (op != null) {
            boogiePrecedence(op);  // will throw exception if operator is unknown.
        }
        this.outermostOp = op;
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
     * @param op a known Boogie operator, or null.
     */
    public void setOpIfWeaker(String op) {
        if (this.outermostOp == null
            || op != null && boogiePrecedence(op) < boogiePrecedence(this.outermostOp)) {
            setOp(op);
        }
    }

    /**
     * Append the given string to this expression.
     *
     * @param str
     */
    public void append(String str) {
        this.builder.append(str);
    }

    public void appendf(String format, Object... args) {
        this.builder.append(String.format(format, args));
    }

    @Override
    public String toString() {
        return this.builder.toString();
    }

    /**
     * Coerce the term to a WVal string.
     *
     * @return a BoogieExpr of type WVal.
     */
    public BoogieExpr asWVal() {
        if (this.termType == BoogieType.WVAL) {
            return this;
        } else {
            final BoogieExpr result = new BoogieExpr(BoogieType.WVAL);
            result.append("from");
            result.append(this.termType.toString());
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
     * @return a BoogieExpr whose type is the requested type.
     */
    public BoogieExpr as(BoogieType type) {
        assert type != BoogieType.WVAL;
        if (this.termType == type) {
            return this;
        } else if (this.termType == BoogieType.WVAL){
            final BoogieExpr result = new BoogieExpr(type);
            result.append("to");
            result.append(type.toString());
            result.append("(");
            result.builder.append(this.builder.toString());
            result.append(")");
            return result;
        } else {
            throw new IllegalArgumentException("Cannot coerce " + this.builder.toString() + " to " + type);
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
            this.builder.append("(");
            this.builder.append(expr.builder);
            this.builder.append(")");
        } else {
            this.builder.append(expr.builder);
        }
    }

    /**
     * Adds expr to this term, without any bracket checking.
     * This automatically calls <pre>setOpIfWeaker(expr.getOp())</pre>.
     *
     * @param expr
     */
    public void addExpr(BoogieExpr expr) {
        this.builder.append(expr.builder);
        setOpIfWeaker(expr.outermostOp);
    }

    /**
     * See if this expression needs parentheses.
     *
     * @param op a known Boogie operator
     * @return true if this expression needs parentheses before applying op to it.
     */
    public boolean needsBrackets(String op) {
        if (this.outermostOp == null) {
            return false;
        }
        final int opPrec = boogiePrecedence(op);
        final int thisPrec = boogiePrecedence(this.outermostOp);
        if (thisPrec > opPrec) {
            // this expr has a tighter-binding operator than op, so no brackets needed.
            return false;
        }
        if (op.equals(this.outermostOp)) {
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
        this.builder.append(op);
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
        this.builder.append(op);
        addAndBracketExpr(rhs, op);
        setOpIfWeaker(op);
    }

    /**
     * Wraps this expression isType parentheses (if necessary) to ensure that it is an atomic expression.
     *
     * @return a BoogieExpr whose outermost operator is null.
     */
    public BoogieExpr asAtom() {
        if (this.outermostOp == null) {
            return this;
        } else {
            return new BoogieExpr(this.termType, "(" + this.toString() + ")");
        }
    }

    /**
     * Returns this expression, but with brackets added around it if necessary.
     * @param op the context where this expression will be used.
     * @return a safe expression for that context.
     */
    public BoogieExpr withBrackets(String op) {
        if (needsBrackets(op)) {
            final BoogieExpr result = new BoogieExpr(this.termType);
            result.addAndBracketExpr(this, op);
            return result;
        } else {
            return this;
        }
    }
}
