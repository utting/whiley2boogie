package wy2boogie.commands;

import java.io.File;
import java.io.IOException;
import java.util.List;

import wy2boogie.core.BoogieFile;
import wy2boogie.tasks.BoogieCompileTask;
import wybs.util.StdBuildRule;
import wybs.util.StdProject;
import wyc.command.Compile;
import wyc.command.Compile.Result;
import wycc.lang.Command;
import wycc.lang.Feature.ConfigurationError;
import wycc.util.ArrayUtils;
import wycc.util.Logger;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.lang.Content.Registry;
import wyfs.util.DirectoryRoot;
import wyc.lang.WhileyFile;

public class Wy2Boogie extends Compile {
	/**
	 * The location in which class generated js files are stored, or null if not
	 * specified.
	 */
	protected DirectoryRoot boogieDir;

	public Wy2Boogie(Registry registry, Logger logger) {
		super(registry, logger);
	}


	private static final String[] SCHEMA = {
			"boogiedir"
	};

	@Override
	public String getName() {
		return "boogie";
	}

	@Override
	public String getDescription() {
		return "Translates WyIL files into the Boogie verification language";
	}

	@Override
	public String[] getOptions() {
		return ArrayUtils.append(super.getOptions(),SCHEMA);
	}

	@Override
	public void set(String option, Object value) throws ConfigurationError {
		try {
			switch(option) {
			case "boogiedir":
				setBoogieDir(new File((String)value));
				break;
			default:
				super.set(option, value);
			}
		} catch(final IOException e) {
			throw new ConfigurationError(e);
		}
	}

	@Override
	public String describe(String option) {
		switch(option) {
		case "boogiedir":
			return "Specify where to place generated Boogie files";
		default:
			return super.describe(option);
		}
	}

	public void setBoogieDir(File dir) throws IOException {
		this.boogieDir = new DirectoryRoot(dir, this.registry);
	}

	@Override
	protected void finaliseConfiguration() throws IOException {
		super.finaliseConfiguration();
		this.boogieDir = getDirectoryRoot(this.boogieDir, this.wyildir);
	}

	@Override
	protected Result compile(StdProject project, List<? extends Path.Entry<?>> entries) {
		try {
			final Result r = super.compile(project, entries);
			this.boogieDir.flush();
			return r;
		} catch (final IOException e) {
			// now what?
			throw new RuntimeException(e);
		}
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
		addWyil2JavaScriptBuildRule(project);
	}

	protected void addWyil2JavaScriptBuildRule(StdProject project) {
		// Configure build rules for normal compilation
		final Content.Filter<WhileyFile> wyilIncludes = Content.filter("**", WhileyFile.BinaryContentType);
		final Content.Filter<WhileyFile> wyilExcludes = null;
		// Rule for compiling Whiley to WyIL
		final BoogieCompileTask boogieBuilder = new BoogieCompileTask(project);
		if(this.verbose) {
			boogieBuilder.setLogger(this.logger);
		}
		project.add(new StdBuildRule(boogieBuilder, this.wyildir, wyilIncludes, wyilExcludes, this.boogieDir));
	}

	@Override
	public List<? extends Path.Entry<?>> getModifiedSourceFiles() throws IOException {
		return getModifiedSourceFiles(this.wyildir, this.wyilIncludes, this.boogieDir, BoogieFile.ContentType);
	}

}
