package wy2boogie.commands;

import wyc.task.CompileTask;
import wycli.cfg.Configuration;
import wycli.cfg.Configuration.Schema;
import wycli.lang.Command;
import wyfs.lang.Path;
import wyfs.util.Trie;
import wyil.lang.WyilFile;
import wyil.lang.WyilFile.Decl;
import wy2boogie.core.*;
import wy2boogie.tasks.BoogieCompileTask;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import wybs.lang.Build;
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
		public Command initialise(Command.Environment environment) {
			return new BoogieCommand(environment, System.out, System.err);
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
	 * Creates a 'boogie' command for the given project.
	 *
	 * TODO: change project from wycc.WyProject to wybs.lang.Build.Project?
	 *
	 * @param project
	 * @param configuration unused, so can be null.
	 * @param sysout
	 * @param syserr
	 */
	public BoogieCommand(Configuration configuration, OutputStream sysout,
			OutputStream syserr) {
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
	public boolean execute(Command.Project project, Template template) throws Exception {
		boolean verbose = template.getOptions().get("verbose", Boolean.class);
		boolean counterexample = template.getOptions().get("counterexample", Boolean.class);
		String output = template.getOptions().get("output", String.class);
		//
		if(counterexample) {
			return translateCounterexample(project,verbose,template.getArguments());
		} else {
			List<Path.Entry<WyilFile>> files = translateAnyWhileyFiles(project, verbose, output, template.getArguments());
			return translateWyilFile(project,verbose,files);
		}
	}

	/**
	 * Tries to ensure that every *.whiley file has been compiled into a corresponding *.wyil file.
	 *
	 * @param verbose
	 * @param output
	 * @param args
	 * @return
	 * @throws Exception
	 */
	public List<Path.Entry<WyilFile>> translateAnyWhileyFiles(Command.Project project, boolean verbose, String output, List<String> args) throws Exception {
		try {
			if (verbose) {
				sysout.println("translateAnyWhileyFiles: " + args + " output=" + output);
			}
			Path.Root projectRoot = project.getRoot();
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
				}
			}
			// Create target for run
			Trie id = Trie.fromString(output.replace(".wyil", ""));
			// TODO: should we create a separate compile task for each *.whiley file?
			Path.Entry<WyilFile> target = createWyilFile(project,id);
			CompileTask task = new CompileTask(project, projectRoot, target, sources);
			boolean ok = task.initialise().apply(Build.NULL_METER);
			if (verbose) {
				sysout.println("whiley compile " + sources + " returns " + ok);
			}
			if (!ok) {
				// FIXME: need a better error reporting mechanism
				syserr.println("Error: while compiling " + sources);
				syserr.println("  program must be free of syntax and type errors before translation to Boogie.");
				System.exit(1);  // abort the whole translation chain.
			}
			// Done
			return Arrays.asList(target);
		} catch(RuntimeException e) {
			throw e;
		} catch (IOException e) {
			// FIXME: need a better error reporting mechanism
			syserr.println("internal failure: " + e.getMessage());
			if (verbose) {
				e.printStackTrace(syserr);
			}
			return Collections.EMPTY_LIST;
		}
	}

	private Path.Entry<BoogieFile> createBoogieFile(Command.Project project, Path.ID id) throws IOException {
		Path.Root projectRoot = project.getRoot();
		// Doesn't exist, so create with default value
		Path.Entry<BoogieFile> target = projectRoot.create(id, BoogieFile.ContentType);
		target.write(new BoogieFile(target, new byte[0]));
		return target;
	}

	private Path.Entry<WyilFile> createWyilFile(Command.Project project, Path.ID id) throws IOException {
		Path.Root projectRoot = project.getRoot();
		Path.Entry<WyilFile> target = projectRoot.get(id, WyilFile.ContentType);
		// Check whether target binary exists or not
		if (target == null) {
			// Doesn't exist, so create with default value
			target = projectRoot.create(id, WyilFile.ContentType);
			WyilFile wf = new WyilFile(target);
			// Create initially empty WyIL module.
			Name name = new Name(id);
			WyilFile.Decl.Module module = new WyilFile.Decl.Module(name, new Tuple<>(), new Tuple<>(), new Tuple<>());
			wf.setRootItem(module);
			target.write(wf);
		}
		return target;
	}

	public boolean translateWyilFile(Command.Project project, boolean verbose, List<Path.Entry<WyilFile>> delta) throws Exception {
		try {
			if (verbose) {
				sysout.println("DEBUG: delta: " + delta);
			}
			// Go through all listed *.wyil files and translate each one to Boogie.
			for (Path.Entry<WyilFile> source : delta) {
				Path.Entry<BoogieFile> target = createBoogieFile(project,source.id());
				BoogieCompileTask task = new BoogieCompileTask(project, target, source);
				task.setVerbose(verbose);
				boolean ok = task.initialise().apply(Build.NULL_METER);
				if (!ok) {
					// FIXME: need a better error reporting mechanism
					if (verbose) {
						syserr.println("Error translating wyil to Boogie: " + source);
					}
					return false;
				}
			}
			return true;
		} catch(RuntimeException e) {
			throw e;
		} catch (IOException e) {
			// FIXME: need a better error reporting mechanism
			syserr.println("internal failure: " + e.getMessage());
			if (verbose) {
				e.printStackTrace(syserr);
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
	public boolean translateCounterexample(Command.Project project, boolean verbose, List<String> args) {
		try {
			Path.Root projectRoot = project.getRoot();
			// Convert command-line arguments to project files
			ArrayList<Path.Entry<BoogieExampleFile>> delta = new ArrayList<>();
			for (String arg : args) {
				// strip extension
				String base = arg.replace(".beg", "");
				Trie trie = Trie.fromString(base);
				//
				if (verbose) {
					sysout.println("DEBUG: base=" + base + " root=" + projectRoot + " trie=" + trie);
				}
				Path.Entry<BoogieExampleFile> entry = projectRoot.get(trie, BoogieExampleFile.ContentType);
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
			syserr.println("internal failure: " + e.getMessage());
			if (verbose) {
				e.printStackTrace(syserr);
			}
			return false;
		}
	}

}
