package wy2boogie.tasks;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import java.util.concurrent.Callable;

import wy2boogie.core.BoogieFile;
import wy2boogie.translate.NotImplementedYet;
import wy2boogie.translate.Wyil2Boogie;
import wybs.lang.Build;
import wybs.util.AbstractBuildTask;
import wyc.io.WhileyFileParser;
import wyc.task.CompileTask;
import wycc.util.Logger;
import wycc.util.Pair;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;
import wyfs.lang.Path.Root;
import wyc.lang.WhileyFile;
import wyfs.util.DirectoryRoot;
import wyil.check.*;
import wyil.lang.Compiler;
import wyil.lang.WyilFile;
import wyil.transform.MoveAnalysis;
import wyil.transform.NameResolution;
import wyil.transform.RecursiveTypeAnalysis;

public class BoogieCompileTask extends AbstractBuildTask<WyilFile, BoogieFile> {


	/**
	 * Specify whether to print verbose progress messages or not
	 */
	private boolean verbose;

	/**
	 * Specify whether verification enabled or not
	 */
	private boolean verification;

	/**
	 * Specify whether counterexample generation is enabled or not
	 */
	private boolean counterexamples;


	public BoogieCompileTask(Build.Project project, Path.Entry<BoogieFile> target,
							 Collection<Path.Entry<WyilFile>> sources) {
		super(project, target, sources);
	}

	public BoogieCompileTask setVerbose(boolean flag) {
		this.verbose = flag;
		return this;
	}

	public BoogieCompileTask setVerification(boolean flag) {
		this.verification = flag;
		return this;
	}

	public BoogieCompileTask setCounterExamples(boolean flag) {
		this.counterexamples = flag;
		return this;
	}

	@Override
	public Callable<Boolean> initialise() throws IOException {
		// Extract target and source files for compilation. This is the component which
		// requires I/O.
		WyilFile[] whileys = new WyilFile[sources.size()];
		for (int i = 0; i != whileys.length; ++i) {
			whileys[i] = sources.get(i).read();
		}
		// Construct the lambda for subsequent execution. This will eventually make its
		// way into some kind of execution pool, possibly for concurrent execution with
		// other tasks.
		return () -> execute(target, whileys);
	}

	/**
	 * The business end of a compilation task. The intention is that this
	 * computation can proceed without performing any blocking I/O. This means it
	 * can be used in e.g. a forkjoin task safely.
	 *
	 * @param target  --- The Boogie being written.
	 * @param sources --- The WyilFile(s) being translated.
	 * @return
	 */
	public boolean execute(Path.Entry<BoogieFile> target, WyilFile... sources) throws IOException {
		// Parse source files into target
		if (sources.length != 1) {
			throw new NotImplementedYet("Cannot compile multiple wyil files yet.", null);
		}
		WyilFile source = sources[0];

		final ByteArrayOutputStream out = new ByteArrayOutputStream();
		final PrintWriter writer = new PrintWriter(out);
		final Wyil2Boogie translator = new Wyil2Boogie(writer);
		translator.setVerbose(verbose);
		translator.apply(source);
		writer.close();
		target.write(new BoogieFile(target, out.toByteArray()));
		return true;
	}

}
