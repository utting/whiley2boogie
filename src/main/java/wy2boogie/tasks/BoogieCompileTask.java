package wy2boogie.tasks;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import wy2boogie.core.BoogieFile;
import wybs.lang.Build;
import wybs.lang.Build.Graph;
import wycc.util.Logger;
import wycc.util.Pair;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;
import wyfs.lang.Path.Root;
import wyil.lang.WyilFile;
import wyil.util.TypeSystem;

public class BoogieCompileTask implements Build.Task {
	/**
	 * The master project for identifying all resources available to the
	 * builder. This includes all modules declared in the project being verified
	 * and/or defined in external resources (e.g. jar files).
	 */
	protected final Build.Project project;

	/**
	 * The type system is useful for managing nominal types and converting them
	 * into their underlying types.
	 */
	protected final TypeSystem typeSystem;

	/**
	 * For logging information.
	 */
	private Logger logger = Logger.NULL;

	public BoogieCompileTask(Build.Project project) {
		this.project = project;
		this.typeSystem = new TypeSystem(project);
	}

	public void setLogger(Logger logger) {
		this.logger = logger;
	}

	@Override
	public Build.Project project() {
		return this.project;
	}

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
			final Path.Entry<WyilFile> source = (Path.Entry<WyilFile>) p.first();
			final Path.Entry<BoogieFile> target = dst.create(source.id(), BoogieFile.ContentType);
			graph.registerDerivation(source, target);
			generatedFiles.add(target);

			// Construct the file
			final BoogieFile contents = build(source, target);

			// Write class file into its destination
			target.write(contents);
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

	private BoogieFile build(Path.Entry<WyilFile> source, Path.Entry<BoogieFile> target) throws IOException {
		new ByteArrayOutputStream();
		//final JavaScriptFileWriter jsfw = new JavaScriptFileWriter(this.project,this.typeSystem,bos);
		//jsfw.apply(read);
		final WyilFile read = source.read();
		final String out = read.toString();
		return new BoogieFile(target,out.getBytes());
	}
}
