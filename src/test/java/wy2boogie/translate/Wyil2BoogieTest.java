package wy2boogie.translate;

import static org.junit.Assert.*;

import java.io.ByteArrayOutputStream;
import java.io.PrintWriter;

import org.junit.Test;

import wy2boogie.translate.Wyil2Boogie;

public class Wyil2BoogieTest {

    @Test
    public void testIndents() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        Wyil2Boogie wy2b = new Wyil2Boogie(new PrintWriter(out));
        assertEquals("            ", wy2b.createIndent(3));
        assertEquals("    ", wy2b.createIndent(1));
        assertEquals("", wy2b.createIndent(0));
    }

}
