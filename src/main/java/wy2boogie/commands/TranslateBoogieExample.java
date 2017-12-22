package wy2boogie.commands;

import wy2boogie.core.BoogieExampleFile;
import wy2boogie.core.BoogieFile;
import wy2boogie.tasks.BoogieCounterExampleTask;
import wybs.util.StdBuildRule;
import wybs.util.StdProject;
import wyc.command.Compile;
import wyc.lang.WhileyFile;
import wycc.util.Logger;
import wyfs.lang.Content;
import wyfs.lang.Content.Registry;
import wyfs.lang.Path;
import wyfs.util.DirectoryRoot;
import wyfs.util.Trie;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class TranslateBoogieExample extends Wy2Boogie {

	public TranslateBoogieExample(Registry registry, Logger logger) {
		super(registry, logger);
	}

	final Content.Filter<BoogieExampleFile> begIncludes = Content.filter("**", BoogieExampleFile.ContentType);
	final Content.Filter<BoogieExampleFile> begExcludes = null;

	@Override
	public String getName() {
		return "boogiemodel";
	}

	@Override
	public String getDescription() {

		return "Translate Boogie counter-examples (*.beg) into Whiley notation (*.wyeg).";
		// TODO: add more help, to explain how to generate the .beg file.
		// + "NOTE:\n"
		// + "  To create the boogie model, use: boogie /printModelToFile:prog.beg /printModel:1 wval.bpl prog.bpl"
		// + "  Then to translate it to Whiley:  wy boogiemodel prog.beg"
		// + "  This will create a human-readable prog.wyeg file which contains Whiley-like notation.";
	}

	/**
	 * Add build rules necessary for compiling whiley source files into binary
	 * wyil files.
	 *
	 * @param project
	 */
	@Override
	protected void addCompilationBuildRules(StdProject project) {
		super.addCompilationBuildRules(project);
		addBoogleExampleBuildRule(project);
	}

	protected void addBoogleExampleBuildRule(StdProject project) {
		// Rule for compiling Boogie counter-examples to Whiley counter-examples.
		final BoogieCounterExampleTask boogieExampleTranslator = new BoogieCounterExampleTask(project);
		if (this.verbose) {
			boogieExampleTranslator.setLogger(this.logger);
		}
		project.add(new StdBuildRule(boogieExampleTranslator, this.boogieDir, begIncludes, begExcludes, this.boogieDir));
	}

	@Override
	public List<? extends Path.Entry<?>> getModifiedSourceFiles() throws IOException {
		return getModifiedSourceFiles(this.boogieDir, this.begIncludes, this.boogieDir, BoogieExampleFile.ContentType);
	}

	/**
	 * Temporarily copied from Compile.execute, because that only seems to work on *.whiley inputs.
	 *
	 * FIXME: we should not need to define this at all. Superclass implementation should be okay.
	 *
	 * @param args
	 * @return
	 */
	@Override
	public Result execute(String... args) {
		try {
			ArrayList<File> delta = new ArrayList<>();
			for (String arg : args) {
				delta.add(new File(arg));
			}

			// FIXME: somehow, needing to use physical files at this point is
			// rather cumbersome. It would be much better if the enclosing
			// framework could handle this aspect for us.
			for (File f : delta) {
				if (!f.exists()) {
					// FIXME: sort this out!
					System.err.println("compile: file not found: " + f.getName());
					return Result.ERRORS;
				}
			}
			// Finalise the configuration before continuing.
			StdProject project = initialiseProject();
			// Determine source files to build

			// I cannot get the default Compile.execute(...) to work for .beg files:
			// (AbstractFolder.get just returns null).
			// List<Path.Entry<BoogieExampleFile>> entries = this.boogieDir.find(delta, BoogieExampleFile.ContentType);

			// so here is a crude hack to do it manually...
			List<Path.Entry<BoogieExampleFile>> entries = new ArrayList<>();
			final String suffix = ".beg";
			for (File f : delta) {
				String module = f.getPath();
				if (module.endsWith(suffix)) {
					module = module.substring(0,
							module.length() - suffix.length());
					Path.ID id = Trie.fromString(module);
					Path.Entry entry = new DirectoryRoot.Entry(id, f);
					BoogieExampleFile eg = new BoogieExampleFile(entry);
					entry.associate(BoogieExampleFile.ContentType, eg);
					entries.add(eg.getEntry());
				}
			}

			// Execute the build over the set of files requested
			return compile(project,entries);
		} catch(RuntimeException e) {
			throw e;
		} catch (IOException e) {
			// FIXME: need a better error reporting mechanism
			System.err.println("internal failure: " + e.getMessage());
			if (verbose) {
				e.printStackTrace(System.err);
			}
			return Result.INTERNAL_FAILURE;
		}
	}

}
