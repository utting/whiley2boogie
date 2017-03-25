package wyboogie;

import static org.junit.Assert.*;

import org.junit.Test;

public class BoogieExprTest {

    @Test
    public void testWVal() {
        BoogieExpr expr = new BoogieExpr();
        expr.append("v");
        expr.append("__1");
        assertEquals(BoogieType.WVAL, expr.getType());
        BoogieExpr w = expr.asWVal();
        assertEquals("v__1", w.toString());
        assertEquals(BoogieType.WVAL, w.getType());
        assertEquals(null, w.getOp());

        BoogieExpr i = expr.as(BoogieType.INT);
        assertEquals("toInt(v__1)", i.toString());
        assertEquals(BoogieType.INT, i.getType());
    }

    @Test
    public void testBool() {
        BoogieExpr expr = new BoogieExpr(BoogieType.BOOL);
        expr.append("v");
        expr.append(" == 0");
        assertEquals(BoogieType.BOOL, expr.getType());

        BoogieExpr w = expr.asWVal();
        assertEquals("fromBool(v == 0)", w.toString());
        assertEquals(BoogieType.WVAL, w.getType());

        BoogieExpr b = expr.as(BoogieType.BOOL);
        assertEquals("v == 0", b.toString());
        assertEquals(BoogieType.BOOL, b.getType());

        try {
            expr.as(BoogieType.INT);
            fail("coercion exception expected");
        } catch (IllegalArgumentException ex) {
            assertEquals("Cannot coerce v == 0 to Int", ex.getMessage());
        }
    }

    @Test
    public void testSetOpIfWeaker() {
        BoogieExpr expr = new BoogieExpr(BoogieType.BOOL, "x == 0");
        assertNull(expr.getOp());
        assertTrue(expr.isAtomic());
        expr.setOpIfWeaker(" == ");
        assertFalse(expr.isAtomic());
        assertEquals(" == ", expr.getOp());
        expr.setOpIfWeaker(" != ");
        expr.setOpIfWeaker(null); // should not change it
        assertEquals(" == ", expr.getOp());
        expr.setOpIfWeaker(" && ");
        assertEquals(" && ", expr.getOp());
        expr.setOp(null);
        assertNull(expr.getOp());
        assertTrue(expr.isAtomic());
    }

    @Test
    public void testIsAssoc() {
        assertTrue(BoogieExpr.isAssociative(" && "));
        assertTrue(BoogieExpr.isAssociative(" || "));
        assertTrue(BoogieExpr.isAssociative(" ++ "));
        assertTrue(BoogieExpr.isAssociative(" + "));
        assertTrue(BoogieExpr.isAssociative(" * "));
        assertFalse(BoogieExpr.isAssociative(" - "));
    }

    @Test
    public void testPrec() {
        assertTrue(BoogieExpr.boogiePrecedence(" <==> ") < BoogieExpr.boogiePrecedence(" ==> "));

        assertTrue(BoogieExpr.boogiePrecedence(" ==> ") < BoogieExpr.boogiePrecedence(" || "));

        assertTrue(BoogieExpr.boogiePrecedence(" || ") == BoogieExpr.boogiePrecedence(" && "));
        assertTrue(BoogieExpr.boogiePrecedence(" || ") < BoogieExpr.boogiePrecedence(" == "));

        assertTrue(BoogieExpr.boogiePrecedence(" == ") == BoogieExpr.boogiePrecedence(" != "));
        assertTrue(BoogieExpr.boogiePrecedence(" == ") == BoogieExpr.boogiePrecedence(" < "));
        assertTrue(BoogieExpr.boogiePrecedence(" == ") == BoogieExpr.boogiePrecedence(" <= "));
        assertTrue(BoogieExpr.boogiePrecedence(" == ") == BoogieExpr.boogiePrecedence(" > "));
        assertTrue(BoogieExpr.boogiePrecedence(" == ") == BoogieExpr.boogiePrecedence(" >= "));
        assertTrue(BoogieExpr.boogiePrecedence(" == ") == BoogieExpr.boogiePrecedence(" <: "));
        assertTrue(BoogieExpr.boogiePrecedence(" == ") < BoogieExpr.boogiePrecedence(" ++ "));

        assertTrue(BoogieExpr.boogiePrecedence(" ++ ") < BoogieExpr.boogiePrecedence(" + "));

        assertTrue(BoogieExpr.boogiePrecedence(" + ") == BoogieExpr.boogiePrecedence(" - ")); //binary
        assertTrue(BoogieExpr.boogiePrecedence(" + ") < BoogieExpr.boogiePrecedence(" * "));

        assertTrue(BoogieExpr.boogiePrecedence(" * ") == BoogieExpr.boogiePrecedence(" / "));
        assertTrue(BoogieExpr.boogiePrecedence(" * ") == BoogieExpr.boogiePrecedence(" % "));
        assertTrue(BoogieExpr.boogiePrecedence(" * ") == BoogieExpr.boogiePrecedence(" div "));
        assertTrue(BoogieExpr.boogiePrecedence(" * ") == BoogieExpr.boogiePrecedence(" mod "));
        assertTrue(BoogieExpr.boogiePrecedence(" * ") < BoogieExpr.boogiePrecedence("! "));

        assertTrue(BoogieExpr.boogiePrecedence("! ") == BoogieExpr.boogiePrecedence("- ")); //unary
        assertTrue(BoogieExpr.boogiePrecedence("! ") < BoogieExpr.boogiePrecedence("["));
    }

    @Test
    public void testInfix() {
        BoogieExpr ex = new BoogieExpr(BoogieType.INT, "x");
        BoogieExpr e2 = new BoogieExpr(BoogieType.INT, "2");
        BoogieExpr e3 = new BoogieExpr(BoogieType.INT, "3");
        BoogieExpr sum = new BoogieExpr(BoogieType.INT);
        sum.addOp(ex, " + ", e2);
        assertEquals("x + 2", sum.toString());
        assertEquals(" + ", sum.getOp());
        assertTrue(sum.needsBrackets(" * "));
        assertTrue(sum.needsBrackets(" - "));
        assertFalse(sum.needsBrackets(" + "));

        BoogieExpr sum2 = new BoogieExpr(BoogieType.INT);
        sum2.addOp(sum, " + ", sum);
        assertEquals("x + 2 + x + 2", sum2.toString());
        assertEquals(" + ", sum2.getOp());

        BoogieExpr prod = new BoogieExpr(BoogieType.INT);
        prod.addOp(sum, " * ", e3);
        assertFalse(prod.needsBrackets(" * "));
        assertFalse(prod.needsBrackets(" + "));
        assertTrue(prod.needsBrackets("- "));
        assertEquals("(x + 2) * 3", prod.toString());
        assertEquals(" * ", prod.getOp());

        assertEquals("(x + 2) * 3", prod.withBrackets(" * ").toString());
        BoogieExpr prod2 = prod.withBrackets("- ");
        assertEquals("((x + 2) * 3)", prod2.toString());
        assertNull(prod2.getOp());
    }

    @Test(expected = IllegalArgumentException.class)
    public void testBadOp() {
        BoogieExpr ex = new BoogieExpr(BoogieType.INT, "x");
        BoogieExpr e2 = new BoogieExpr(BoogieType.INT, "2");
        BoogieExpr sum = new BoogieExpr(BoogieType.INT);
        sum.addOp(ex, " + ", e2);
        sum.needsBrackets("+");
    }

    @Test
    public void testNeedsBrackets() {
        String[] ops = { " <==> ", " ==> ", " || ", " && ", " != ", " - ", " / ", "- " };
        for (int i = 0; i < ops.length; i++) {
            for (int j = 0; j < ops.length; j++) {
                BoogieExpr ex = new BoogieExpr(BoogieType.INT, "x");
                BoogieExpr e2 = new BoogieExpr(BoogieType.INT, "2");
                BoogieExpr expr = new BoogieExpr(BoogieType.INT);
                expr.addOp(ex, ops[i], e2);
                if (2 <= Math.min(i, j) && Math.max(i, j) <= 3) {
                    // && and || have the same precedence in Boogie.
                    // So brackets are always needed, except when the inner and outer operator are the same.
                    assertEquals(i != j, expr.needsBrackets(ops[j]));
                } else {
                    assertEquals(i <= j, expr.needsBrackets(ops[j]));
                }
            }
        }
    }
}
