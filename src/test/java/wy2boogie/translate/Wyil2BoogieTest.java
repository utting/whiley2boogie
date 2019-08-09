package wy2boogie.translate;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintWriter;
import java.util.List;


public class Wyil2BoogieTest {

    @Test
    public void testIndents() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        Wyil2Boogie wy2b = new Wyil2Boogie(new PrintWriter(out));
        assertEquals("            ", wy2b.createIndent(3));
        assertEquals("    ", wy2b.createIndent(1));
        assertEquals("", wy2b.createIndent(0));
    }

    @Test
    public void testCommaSep() {
        Wyil2Boogie wy2b = new Wyil2Boogie(System.err);
        assertEquals("", wy2b.commaSep());
        assertEquals("a", wy2b.commaSep("", "a", ""));
        assertEquals("a, bb, !!", wy2b.commaSep("a", "bb", "!!"));
        assertEquals("a, b", wy2b.commaSep("a", "", "b"));
    }

    @Test
    public void testCommaSepMap() {
        Wyil2Boogie wy2b = new Wyil2Boogie(System.err);
        String[] vals = {"1","0","5"};
        List<String> strs = List.of(vals);
        assertEquals("1, 0, 5", wy2b.commaSepMap(strs, s -> s));
        assertEquals(", , ", wy2b.commaSepMap(strs, s -> ""));
        assertEquals("1, , 5", wy2b.commaSepMap(strs, s -> s.equals("0") ? "" : s));
    }
}
