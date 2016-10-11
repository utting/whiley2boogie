package wyboogie;

public enum BoogieType {
    WVAL("WVal"),
    NULL("Null"),
    INT("Int"),
    BOOL("Bool"),
    ARRAY("Array"),
    RECORD("Record");
    // TODO REF, FUNCTION, METHOD

    private final String boogieName;

    BoogieType(String name) {
        boogieName = name;
    }

    @Override
    public String toString() {
        return boogieName;
    }
}
