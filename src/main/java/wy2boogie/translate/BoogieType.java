package wy2boogie.translate;

public enum BoogieType {
    WVAL("WVal"),
    NULL("Null"),
    INT("Int"),
    BOOL("Bool"),
    ARRAY("Array"),
    RECORD("Record"),
    FUNCTION("Function"),
    METHOD("Method"),
    WREF("Ref");

    private final String boogieName;

    BoogieType(String name) {
        boogieName = name;
    }

    @Override
    public String toString() {
        return boogieName;
    }
}
