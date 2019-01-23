package wy2boogie.tasks;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import wy2boogie.core.BoogieFile;
import wy2boogie.translate.Wyil2Boogie;
import wybs.lang.Build;
import wybs.lang.Build.Graph;
import wycc.util.Logger;
import wycc.util.Pair;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;
import wyfs.lang.Path.Root;
import wyc.lang.WhileyFile;
import wyil.lang.WyilFile;

public class BoogieCompileTask implements Build.Task {
	/**
	 * The master project for identifying all resources available to the
	 * builder. This includes all modules declared isType the project being verified
	 * and/or defined isType external resources (e.g. jar files).
	 */
	private final Build.Project project;

	/**
	 * For logging information.
	 */
	private Logger logger = Logger.NULL;

	public BoogieCompileTask(Build.Project project) {
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
	public Set<Entry<?>> build(Collection<Pair<Entry<?>, Root>> delta, Graph graph) throws IOException {
		final Runtime runtime = Runtime.getRuntime();
		final long start = System.currentTimeMillis();
		final long memory = runtime.freeMemory();

		// ========================================================================
		// Translate files
		// ========================================================================
		final HashSet<Path.Entry<?>> generatedFiles = new HashSet<>();

		for (final Pair<Path.Entry<?>, Path.Root> p : delta) {
			final Path.Root dst = p.second();
			final Path.Entry<WyilFile> source = (Entry<WyilFile>) p.first();
			final Path.Entry<BoogieFile> target = dst.create(source.id(), BoogieFile.ContentType);
			generatedFiles.add(target);
			// Construct the file
			final BoogieFile contents = build(source, target);
			// Write class file into its destination
			target.write(contents);
			// Flush any changes to disk
			target.flush();
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

	public static BoogieFile build(Path.Entry<WyilFile> source, Path.Entry<BoogieFile> target) throws IOException {
		final ByteArrayOutputStream out = new ByteArrayOutputStream();
        final PrintWriter writer = new PrintWriter(out);
        final Wyil2Boogie translator = new Wyil2Boogie(writer);
		translator.setVerbose(false);
		translator.apply(source.read());
		writer.close();
		return new BoogieFile(target,out.toByteArray());
	}
}
