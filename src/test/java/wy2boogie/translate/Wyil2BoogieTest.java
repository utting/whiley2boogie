package wy2boogie.translate;

import static org.junit.Assert.*;

import java.io.ByteArrayOutputStream;
import java.io.PrintWriter;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import wybs.util.StdProject;
import wyil.check.FlowTypeCheck;
import wyil.lang.WyilFile.Type;

public class Wyil2BoogieTest {

    @Before
    public void setup() {

    }

    @Test
    public void testIndents() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        Wyil2Boogie wy2b = new Wyil2Boogie(new PrintWriter(out));
        assertEquals("            ", wy2b.createIndent(3));
        assertEquals("    ", wy2b.createIndent(1));
        assertEquals("", wy2b.createIndent(0));
    }
}
