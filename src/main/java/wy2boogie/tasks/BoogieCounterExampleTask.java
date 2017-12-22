package wy2boogie.tasks;

import wy2boogie.core.BoogieExampleFile;
import wy2boogie.core.BoogieFile;
import wy2boogie.core.WhileyExampleFile;
import wy2boogie.translate.Wyil2Boogie;
import wybs.lang.Build;
import wybs.util.StdProject;
import wyc.lang.WhileyFile;
import wycc.util.Logger;
import wycc.util.Pair;
import wyfs.lang.Path;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

public class BoogieCounterExampleTask implements Build.Task {
    /**
     * The master project for identifying all resources available to the
     * builder. This includes all modules declared in the project being verified
     * and/or defined in external resources (e.g. jar files).
     */
    private final Build.Project project;

    /**
     * For logging information.
     */
    private Logger logger = Logger.NULL;


    public BoogieCounterExampleTask(StdProject project) {
        super();
        this.project = project;
    }


    public void setLogger(Logger logger) {
        this.logger = logger;
    }

    @Override
    public Build.Project project() {
        return this.project;
    }

    @SuppressWarnings("unchecked")
    @Override
    public Set<Path.Entry<?>> build(Collection<Pair<Path.Entry<?>, Path.Root>> delta, Build.Graph graph) throws IOException {
        final Runtime runtime = Runtime.getRuntime();
        final long start = System.currentTimeMillis();
        final long memory = runtime.freeMemory();

        // ========================================================================
        // Translate files
        // ========================================================================
        final HashSet<Path.Entry<?>> generatedFiles = new HashSet<>();


        System.out.println("starting build:");
        for (final Pair<Path.Entry<?>, Path.Root> p : delta) {
            final Path.Root dst = p.second();
            final Path.Entry<BoogieExampleFile> source = (Path.Entry<BoogieExampleFile>) p.first();
            final Path.Entry<WhileyExampleFile> target = dst.create(source.id(), WhileyExampleFile.ContentType);

            System.out.println("  source=" + source);
            System.out.println("  target=" + target);

            graph.registerDerivation(source, target);
            generatedFiles.add(target);

            // Construct the file
            final WhileyExampleFile contents = build(source, target);

            // Write class file into its destination
            target.write(contents);
            System.out.println("  wrote contents=" + contents);
        }

        // ========================================================================
        // Done
        // ========================================================================

        final long endTime = System.currentTimeMillis();
        this.logger.logTimedMessage("WyIL => Boogie: compiled " + delta.size() + " file(s)",
                endTime - start,
                memory - runtime.freeMemory());

        return generatedFiles;
    }

    private WhileyExampleFile build(Path.Entry<BoogieExampleFile> source, Path.Entry<WhileyExampleFile> target) throws IOException {
        final ByteArrayOutputStream out = new ByteArrayOutputStream();
        final PrintWriter writer = new PrintWriter(out);
        BoogieExampleFile eg = source.read();
        writer.println("TODO: translate the example!!!!!!!!!!");
        writer.close();
        return new WhileyExampleFile(target,out.toByteArray());
    }


}
