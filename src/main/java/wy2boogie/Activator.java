package wy2boogie;

import wycc.cfg.Configuration;

import java.io.IOException;

import wy2boogie.commands.BoogieCommand;
import wy2boogie.core.BoogieExampleFile;
import wy2boogie.core.BoogieFile;
import wy2boogie.core.WhileyExampleFile;
import wy2boogie.tasks.BoogieCompileTask;
import wybs.lang.Build;
import wybs.lang.Build.Graph;
import wybs.util.AbstractCompilationUnit.Value;
import wycc.lang.Command;
import wycc.lang.Module;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.util.Trie;
import wyil.lang.WyilFile;

/**
 * Plugin for the Whiley to Boogie translator.
 *
 * Adapted from the Whiley2JavaScript backend.
 *
 * @author Mark Utting
 */
public class Activator implements Module.Activator {
	public static Trie PKGNAME_CONFIG_OPTION = Trie.fromString("package/name");
	public static Trie SOURCE_CONFIG_OPTION = Trie.fromString("build/whiley/target");
	public static Trie TARGET_CONFIG_OPTION = Trie.fromString("build/boogie/target");
	private static Value.UTF8 SOURCE_DEFAULT = new Value.UTF8("src".getBytes());
	private static Value.UTF8 TARGET_DEFAULT = new Value.UTF8("bin".getBytes());

	public static Build.Platform BOOGIE_PLATFORM = new Build.Platform() {
		private Trie pkg;
		//
		private Trie source;
		// Specify directory where generated WyIL files are dumped.
		private Trie target;
		//
		@Override
		public String getName() {
			return "boogie";
		}

		@Override
		public Configuration.Schema getConfigurationSchema() {
			return Configuration.fromArray(
					Configuration.UNBOUND_STRING(SOURCE_CONFIG_OPTION, "Specify location for wyil binary files", SOURCE_DEFAULT),
					Configuration.UNBOUND_STRING(TARGET_CONFIG_OPTION, "Specify location for generated boogie files", TARGET_DEFAULT));
		}

		@Override
		public void apply(Configuration configuration) {
			// Extract source path
			this.pkg = Trie.fromString(configuration.get(Value.UTF8.class, PKGNAME_CONFIG_OPTION).unwrap());
			this.source = Trie.fromString(configuration.get(Value.UTF8.class, SOURCE_CONFIG_OPTION).unwrap());
			this.target = Trie.fromString(configuration.get(Value.UTF8.class, TARGET_CONFIG_OPTION).unwrap());
		}

		@Override
		public Build.Task initialise(Build.Project project) {
			return new BoogieCompileTask(project);
		}

		@Override
		public Content.Type<?> getSourceType() {
			return WyilFile.ContentType;
		}

		@Override
		public Content.Type<?> getTargetType() {
			return BoogieFile.ContentType;
		}

		@Override
		public Content.Filter<?> getSourceFilter() {
			return Content.filter("**", WyilFile.ContentType);
		}

		@Override
		public Content.Filter<?> getTargetFilter() {
			return Content.filter("**", BoogieFile.ContentType);
		}

		@Override
		public Path.Root getSourceRoot(Path.Root root) throws IOException {
			return root.createRelativeRoot(source);
		}

		@Override
		public Path.Root getTargetRoot(Path.Root root) throws IOException {
			return root.createRelativeRoot(target);
		}

		@Override
		public void refresh(Graph graph, Path.Root src, Path.Root bin) throws IOException {
			//
			Path.Entry<BoogieFile> binary = bin.get(pkg, BoogieFile.ContentType);
			// Check whether target binary exists or not
			if (binary == null) {
				// Doesn't exist, so create with default value
				binary = bin.create(pkg, BoogieFile.ContentType);
				BoogieFile wf = new BoogieFile(binary, new byte[0]);
				binary.write(wf);
			}
			//
			for (Path.Entry<?> source : src.get(getSourceFilter())) {
				// Register this derivation
				graph.connect(source, binary);
			}
			//
		}

		@Override
		public void execute(Build.Project project, Path.ID id, String method, Value... args) throws IOException {
			// FIXME: what to do here?
		}
	};

	public static Build.Platform BOOGIE_EXAMPLE_PLATFORM = new Build.Platform() {
		private Trie pkg;
		//
		private Trie source;
		// Specify directory where generated WyIL files are dumped.
		private Trie target;
		//
		@Override
		public String getName() {
			return "boogie-counterexample";
		}

		@Override
		public Configuration.Schema getConfigurationSchema() {
			return Configuration.fromArray(
					Configuration.UNBOUND_STRING(SOURCE_CONFIG_OPTION, "Specify location for wyil binary files", SOURCE_DEFAULT),
					Configuration.UNBOUND_STRING(TARGET_CONFIG_OPTION, "Specify location for generated boogie files", TARGET_DEFAULT));
		}

		@Override
		public void apply(Configuration configuration) {
			// Extract source path
			this.pkg = Trie.fromString(configuration.get(Value.UTF8.class, PKGNAME_CONFIG_OPTION).unwrap());
			this.source = Trie.fromString(configuration.get(Value.UTF8.class, SOURCE_CONFIG_OPTION).unwrap());
			this.target = Trie.fromString(configuration.get(Value.UTF8.class, TARGET_CONFIG_OPTION).unwrap());
		}

		@Override
		public Build.Task initialise(Build.Project project) {
			return new BoogieCompileTask(project);
		}

		@Override
		public Content.Type<?> getSourceType() {
			return BoogieExampleFile.ContentType;
		}

		@Override
		public Content.Type<?> getTargetType() {
			return WhileyExampleFile.ContentType;
		}

		@Override
		public Content.Filter<?> getSourceFilter() {
			return Content.filter("**", BoogieExampleFile.ContentType);
		}

		@Override
		public Content.Filter<?> getTargetFilter() {
			return Content.filter("**", WhileyExampleFile.ContentType);
		}

		@Override
		public Path.Root getSourceRoot(Path.Root root) throws IOException {
			return root.createRelativeRoot(source);
		}

		@Override
		public Path.Root getTargetRoot(Path.Root root) throws IOException {
			return root.createRelativeRoot(target);
		}

		@Override
		public void refresh(Graph graph, Path.Root src, Path.Root bin) throws IOException {
			//
			Path.Entry<WhileyExampleFile> binary = bin.get(pkg, WhileyExampleFile.ContentType);
			// Check whether target binary exists or not
			if (binary == null) {
				// Doesn't exist, so create with default value
				binary = bin.create(pkg, WhileyExampleFile.ContentType);
				WhileyExampleFile wf = new WhileyExampleFile(binary, new byte[0]);
				binary.write(wf);
			}
			//
			for (Path.Entry<?> source : src.get(getSourceFilter())) {
				// Register this derivation
				graph.connect(source, binary);
			}
			//
		}

		@Override
		public void execute(Build.Project project, Path.ID id, String method, Value... args) throws IOException {
			// FIXME: what to do here?
		}
	};


	// =======================================================================
	// Start
	// =======================================================================

	@Override
	public Module start(Module.Context context) {
		// List of platforms to make available
		context.register(Build.Platform.class, BOOGIE_PLATFORM);
		context.register(Build.Platform.class, BOOGIE_EXAMPLE_PLATFORM);
		// List of commands to make available
		context.register(Command.Descriptor.class, BoogieCommand.DESCRIPTOR);
		// List of content types
		context.register(Content.Type.class, BoogieFile.ContentType);
		context.register(Content.Type.class, BoogieExampleFile.ContentType);
		context.register(Content.Type.class, WhileyExampleFile.ContentType);
		// Done
		return new Module() {
			// what goes here?
		};
	}

	// =======================================================================
	// Stop
	// =======================================================================

	@Override
	public void stop(Module module, Module.Context context) {
		// could do more here?
	}
}
