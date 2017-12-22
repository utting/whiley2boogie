package wy2boogie.core;

import wybs.lang.CompilationUnit;
import wybs.util.AbstractCompilationUnit;
import wyfs.lang.Content;
import wyfs.lang.Path;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

public class BoogieExampleFile extends AbstractCompilationUnit {
	// =========================================================================
	// Content Type
	// =========================================================================

	/**
	 * Raw contents of the counter-example file.
	 */
	private final String[] models = new String[0];

	/**
	 * Responsible for identifying and writing Whiley counter-example models.
	 * The normal extension is ".wyeg" for Whiley counter-examples.
	 */
	public static final Content.Type<BoogieExampleFile> ContentType = new Content.Type<BoogieExampleFile>() {
		public Path.Entry<BoogieExampleFile> accept(Path.Entry<?> e) {
			if (e.contentType() == this) {
				return (Path.Entry<BoogieExampleFile>) e;
			}
			return null;
		}

		@Override
		public BoogieExampleFile read(Path.Entry<BoogieExampleFile> e, InputStream input) throws IOException {
			// TODO: read contents
			throw new UnsupportedOperationException();
		}

		@Override
		public void write(OutputStream output, BoogieExampleFile jf) {
			throw new UnsupportedOperationException();
		}

		@Override
		public String toString() {
			return "Content-Type: Boogie counter-examples";
		}

		@Override
		public String getSuffix() {
			return "beg";
		}
	};

	public BoogieExampleFile(Path.Entry<? extends CompilationUnit> entry) {
		super(entry);
	}

	public String[] getModels() {
		return models;
	}

	@Override
	public String toString() {
		return models.length + " models";
	}
}
