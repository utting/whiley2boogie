package wy2boogie.core;

import wybs.lang.CompilationUnit;
import wybs.util.AbstractCompilationUnit;
import wyfs.lang.Content;
import wyfs.lang.Path;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

public class WhileyExampleFile extends AbstractCompilationUnit {
	// =========================================================================
	// Content Type
	// =========================================================================

	/**
	 * Responsible for identifying and writing Whiley counter-example models.
	 * The normal extension is ".wyeg" for Whiley counter-examples.
	 */
	public static final Content.Type<WhileyExampleFile> ContentType = new Content.Type<WhileyExampleFile>() {
		public Path.Entry<WhileyExampleFile> accept(Path.Entry<?> e) {
			if (e.contentType() == this) {
				return (Path.Entry<WhileyExampleFile>) e;
			}
			return null;
		}

		@Override
		public WhileyExampleFile read(Path.Entry<WhileyExampleFile> e, InputStream input) throws IOException {
			// At this stage, parsing example files is strictly off-limits :)
			throw new UnsupportedOperationException();
		}

		@Override
		public void write(OutputStream output, WhileyExampleFile jf) throws IOException {
			output.write(jf.bytes);
		}

		@Override
		public String toString() {
			return "Content-Type: whiley counter-example";
		}

		@Override
		public String getSuffix() {
			return "wyeg";
		}
	};

	/**
	 * Raw contents of the counter-example file.
	 */
	private final byte[] bytes;

	public WhileyExampleFile(Path.Entry<? extends CompilationUnit> entry, byte[] bytes) {
		super(entry);
		this.bytes = bytes;
	}

	public byte[] getBytes() {
		return this.bytes;
	}

	@Override
	public String toString() {
		return new String(this.bytes);
	}
}
