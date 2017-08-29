package wy2boogie.translate;

import static org.junit.Assert.*;

import org.junit.Test;

import wy2boogie.translate.BoogieType;

public class BoogieTypeTest {

    @Test
    public void testToString() {
        assertEquals("WVAL", BoogieType.WVAL.name());
        assertEquals("WVal", BoogieType.WVAL.toString());
        assertEquals("INT", BoogieType.INT.name());
        assertEquals("Int", BoogieType.INT.toString());
        assertEquals("Null", BoogieType.NULL.toString());
        assertEquals("Bool", BoogieType.BOOL.toString());
        assertEquals("Array", BoogieType.ARRAY.toString());
        assertEquals("Record", BoogieType.RECORD.toString());
    }
}
