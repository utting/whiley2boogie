package wy2boogie.translate;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintWriter;


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
