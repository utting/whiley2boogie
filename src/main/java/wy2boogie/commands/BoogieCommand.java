package wy2boogie.commands;

import wycc.WyProject;
import wycc.cfg.Configuration;
import wycc.cfg.Configuration.Schema;
import wycc.lang.Command;
import wycc.util.Logger;
import wycc.util.Pair;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;
import wyfs.lang.Path.Root;
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
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import wybs.lang.Build;
import wybs.lang.Build.Graph;
import wybs.lang.Build.Project;
import wybs.util.StdProject;
import wybs.util.AbstractCompilationUnit.Name;
import wybs.util.AbstractCompilationUnit.Tuple;
import wyc.lang.WhileyFile;

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
					Command.OPTION_FLAG("verbose", "generate verbose information about the build", false),
					Command.OPTION_STRING("output", "specific output file", "a.wyil"));
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
		String output = template.getOptions().get("output", String.class);
		//
		if(counterexample) {
			return translateCounterexample(verbose,template.getArguments());
		} else {
			List<String> files = translateAnyWhileyFiles(verbose,output,template.getArguments());
			return translateWyilFile(verbose,files);
		}
	}

	public List<String> translateAnyWhileyFiles(boolean verbose, String output, List<String> args) {
		try {
			Path.Root projectRoot = project.getBuildProject().getRoot();
			List<String> files = new ArrayList<>();
			List<Path.Entry<WhileyFile>> sources = new ArrayList<>();
			// Identify and read in any source files
			for(int i=0;i!=args.size();++i) {
				String arg = args.get(i);
				if(arg.endsWith(".whiley")) {
					// Strip extension
					arg = arg.replace(".whiley", "");
					//	Find the source file in question
					Path.Entry<WhileyFile> source = projectRoot.get(Trie.fromString(arg), WhileyFile.ContentType);
					if(source == null) {
						syserr.println("ignoring missing file " + arg);
					} else {
						sources.add(source);
					}
				} else {
					files.add(arg);
				}
			}
			// Create target for run
			Trie id = Trie.fromString(output.replace(".wyil", ""));
			files.add(output);
			Path.Entry<WyilFile> target = createWyilFile(id);
			// System.out.println("GOT: " + target);
			// Reuse code from the compile task for this purpose
			wyc.task.CompileTask.build(Logger.NULL, project.getBuildProject(), target, sources);
			// Done
			return files;
		} catch(RuntimeException e) {
			throw e;
		} catch (IOException e) {
			// FIXME: need a better error reporting mechanism
			System.err.println("internal failure: " + e.getMessage());
			if (verbose) {
				e.printStackTrace(System.err);
			}
			return Collections.EMPTY_LIST;
		}
	}

	private Path.Entry<WyilFile> createWyilFile(Path.ID id) throws IOException {
		Path.Root projectRoot = project.getBuildProject().getRoot();
		Path.Entry<WyilFile> target = projectRoot.get(id, WyilFile.ContentType);
		// Check whether target binary exists or not
		if (target == null) {
			// Doesn't exist, so create with default value
			target = projectRoot.create(id, WyilFile.ContentType);
			WyilFile wf = new WyilFile(target);
			target.write(wf);
			// Create initially empty WyIL module.
			wf.setRootItem(new WyilFile.Decl.Module(new Name(id), new Tuple<>(), new Tuple<>()));
		}
		return target;
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
				String base = arg.replace(".beg", "");
				//
				Path.Entry<BoogieExampleFile> entry = projectRoot.get(Trie.fromString(base), BoogieExampleFile.ContentType);
				if (entry == null) {
					throw new RuntimeException("Cannot create Path.Entry for " + arg + ".  Try .beg?");
				}
				delta.add(entry);
			}
			// Go through all listed beg files and translate them
			for (Path.Entry<BoogieExampleFile> f : delta) {
				BoogieExampleFile beg = f.read();
				final ByteArrayOutputStream out = new ByteArrayOutputStream();
		        final PrintWriter writer = new PrintWriter(out);
		        writer.print(beg.toString());
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
