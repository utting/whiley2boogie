package wy2boogie.translate;

import static org.junit.Assert.*;

import java.io.ByteArrayOutputStream;
import java.io.PrintWriter;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import wybs.lang.NameResolver;
import wybs.util.StdProject;
import wyc.check.FlowTypeCheck;
import wyc.lang.WhileyFile.Type;
import wyil.type.TypeSystem;

public class Wyil2BoogieTest {
    private StdProject project;
    private TypeSystem typeSystem;

    @Before
    public void setup() {
        project = new StdProject();
        typeSystem = new TypeSystem(project);
    }

    @Test
    public void testIndents() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        Wyil2Boogie wy2b = new Wyil2Boogie(typeSystem, new PrintWriter(out));
        assertEquals("            ", wy2b.createIndent(3));
        assertEquals("    ", wy2b.createIndent(1));
        assertEquals("", wy2b.createIndent(0));
    }

    @Ignore
    @Test
    public void testEquality() {
        Type leftType = Type.Int;
        Type rightType = Type.Int;
        Type intersectType = new Type.Intersection(leftType, rightType);
        Type eqType = null;
        try {
            // this returns null currently...
            eqType = this.typeSystem.extractReadableType(intersectType, new FlowTypeCheck.Environment());
        } catch (NameResolver.ResolutionError resolutionError) {
            resolutionError.printStackTrace();
        }
        assertEquals(Type.Int, eqType);
    }
}
