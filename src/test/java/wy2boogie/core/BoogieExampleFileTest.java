package wy2boogie.core;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

import wyfs.lang.Path;
import wyfs.util.DirectoryRoot;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

public class BoogieExampleFileTest {

    /**
     * Helper method that takes the *.beg input and tests that it translates to the corresponding *.wyeg.
     *
     * @param begFile  Relative path to Boogie Counter Example file with name ending in ".beg".
     * @throws IOException
     */
    private void checkCounterExample(File begFile) throws IOException {
        File expectFile = new File(begFile.getPath().replace(".beg", ".wyeg_correct"));
        Path.Entry<BoogieExampleFile> source = new DirectoryRoot.Entry<>(null, begFile);
        String expect = new String (Files.readAllBytes(expectFile.toPath()));
        BoogieExampleFile beg = BoogieExampleFile.ContentType.read(source, source.inputStream());
        assertEquals(expect, beg.toString());
    }

    /** Basic variables and function. */
    @Test
    public void testFunctionValid6() throws IOException {
        checkCounterExample(new File("tests/counter_example/Function_Valid_6.beg"));
    }

    /** A series of simple records. */
    @Test
    public void testLength() throws IOException {
        checkCounterExample(new File("tests/counter_example/length.beg"));
    }

    /** A series of array values. */
    @Test
    public void testConstrainedList8() throws IOException {
        checkCounterExample(new File("tests/counter_example/ConstrainedList_Valid_8.beg"));
    }

}