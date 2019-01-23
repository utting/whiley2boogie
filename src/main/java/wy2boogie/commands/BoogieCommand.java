package wy2boogie.commands;

import wycc.WyProject;
import wycc.cfg.Configuration;
import wycc.cfg.Configuration.Schema;
import wycc.lang.Command;
import wyfs.lang.Path;
import wyfs.util.DirectoryRoot;
import wyfs.util.Trie;
import wyil.lang.WyilFile;
import wy2boogie.core.*;
import wy2boogie.tasks.BoogieCompileTask;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import wybs.util.StdProject;

public class BoogieCommand implements Command {
	/**
	 * The descriptor for this command.
	 */
	public static final Command.Descriptor DESCRIPTOR = new Command.Descriptor() {

		@Override
		public String getName() {
			return "boogie";
		}

		@Override
		public String getDescription() {
			return "Translate WyIL files into Boogie, and convert counterexamples.";
		}

		@Override
		public List<Command.Option.Descriptor> getOptionDescriptors() {
			return Arrays.asList(Command.OPTION_FLAG("counterexample", "convert a Boogie counterexample (beg) file to a Whiley-like form (wyeg)", false),
					Command.OPTION_FLAG("verbose", "generate verbose information about the build", false));
		}

		@Override
		public Schema getConfigurationSchema() {
			return Configuration.EMPTY_SCHEMA;
		}

		@Override
		public List<Descriptor> getCommands() {
			return Collections.EMPTY_LIST;
		}

		@Override
		public Command initialise(Command parent, Configuration configuration) {
			return new BoogieCommand((WyProject) parent, configuration, System.out, System.err);
		}
	};


	/**
	 * Provides a generic place to which normal output should be directed. This
	 * should eventually be replaced.
	 */
	private final PrintStream sysout;

	/**
	 * Provides a generic place to which error output should be directed. This
	 * should eventually be replaced.
	 */
	private final PrintStream syserr;

	/**
	 * The enclosing project for this build
	 */
	private final WyProject project;

	public BoogieCommand(WyProject project, Configuration configuration, OutputStream sysout,
			OutputStream syserr) {
		this.project = project;
		this.sysout = new PrintStream(sysout);
		this.syserr = new PrintStream(syserr);
	}


	@Override
	public Descriptor getDescriptor() {
		return DESCRIPTOR;
	}

	@Override
	public void initialise() {
		// Don't need to do anything here
	}

	@Override
	public void finalise() {
		// Don't need to do anything here
	}

	@Override
	public boolean execute(Template template) throws Exception {
		boolean verbose = template.getOptions().get("verbose", Boolean.class);
		boolean counterexample = template.getOptions().get("counterexample", Boolean.class);
		//
		if(counterexample) {
			return translateCounterexample(verbose,template.getArguments());
		} else {
			return translateWyilFile(verbose,template.getArguments());
		}
	}

	public boolean translateWyilFile(boolean verbose, List<String> args) {
		try {
			Path.Root projectRoot = project.getBuildProject().getRoot();
			// Convert command-line arguments to project files
			ArrayList<Path.Entry<WyilFile>> delta = new ArrayList<>();
			for (String arg : args) {
				// strip extension
				arg = arg.replace(".wyil", "");
				//
				delta.add(projectRoot.get(Trie.fromString(arg), WyilFile.ContentType));
			}
			// Go through all listed beg files and translate them
			for (Path.Entry<WyilFile> source : delta) {
				// Create target file
				Path.Entry<BoogieFile> target = projectRoot.create(source.id(), BoogieFile.ContentType);
				// Construct the file
				final BoogieFile contents = BoogieCompileTask.build(source, target);
				// Write class file into its destination
				target.write(contents);
				// Flush any changes to disk
				target.flush();
			}
			// Execute the build over the set of files requested
			return true;
		} catch(RuntimeException e) {
			throw e;
		} catch (IOException e) {
			// FIXME: need a better error reporting mechanism
			System.err.println("internal failure: " + e.getMessage());
			if (verbose) {
				e.printStackTrace(System.err);
			}
			return false;
		}
	}

	/**
	 * Temporarily copied from Compile.execute, because that only seems to work on *.whiley inputs.
	 *
	 * FIXME: we should not need to define this at all. Superclass implementation should be okay.
	 *
	 * @param args
	 * @return
	 */
	public boolean translateCounterexample(boolean verbose, List<String> args) {
		try {
			Path.Root projectRoot = project.getBuildProject().getRoot();
			// Convert command-line arguments to project files
			ArrayList<Path.Entry<BoogieExampleFile>> delta = new ArrayList<>();
			for (String arg : args) {
				// strip extension
				arg = arg.replace(".beg", "");
				//
				delta.add(projectRoot.get(Trie.fromString(arg), BoogieExampleFile.ContentType));
			}
			// Go through all listed beg files and translate them
			for (Path.Entry<BoogieExampleFile> f : delta) {
				BoogieExampleFile beg = f.read();
				final ByteArrayOutputStream out = new ByteArrayOutputStream();
		        final PrintWriter writer = new PrintWriter(out);
		        writer.println(beg.toString());
		        writer.close();
		        Path.Entry<WhileyExampleFile> target = projectRoot.create(f.id(), WhileyExampleFile.ContentType);
		        target.write(new WhileyExampleFile(target, out.toByteArray()));
		        target.flush();
			}
			// Execute the build over the set of files requested
			return true;
		} catch(RuntimeException e) {
			throw e;
		} catch (IOException e) {
			// FIXME: need a better error reporting mechanism
			System.err.println("internal failure: " + e.getMessage());
			if (verbose) {
				e.printStackTrace(System.err);
			}
			return false;
		}
	}

}
