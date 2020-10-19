package wy2boogie.core;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import wybs.lang.CompilationUnit;
import wybs.util.AbstractCompilationUnit;
import wyfs.lang.Content;
import wyfs.lang.Path;

public class BoogieFile extends AbstractCompilationUnit<BoogieFile> {
	// =========================================================================
	// Content Type
	// =========================================================================

	/**
	 * Responsible for identifying and reading/writing Boogie files. The normal
	 * extension is ".bpl" for WyilFiles.
	 */
	public static final Content.Type<BoogieFile> ContentType = new Content.Type<BoogieFile>() {
		public Path.Entry<BoogieFile> accept(Path.Entry<?> e) {
			if (e.contentType() == this) {
				return (Path.Entry<BoogieFile>) e;
			}
			return null;
		}

		@Override
		public BoogieFile read(Path.Entry<BoogieFile> e, InputStream input) throws IOException {
			// At this stage, parsing Boogie is strictly off-limits :)
			throw new UnsupportedOperationException();
		}

		@Override
		public void write(OutputStream output, BoogieFile jf) throws IOException {
			output.write(jf.bytes);
			output.flush();
		}

		@Override
		public String toString() {
			return "Content-Type: boogie";
		}

		@Override
		public String getSuffix() {
			return "bpl";
		}
	};

	/**
	 * Raw contents of the Boogie file.
	 */
	private byte[] bytes;

	public BoogieFile(Path.Entry<BoogieFile> entry, byte[] bytes) {
		super(entry);
		this.bytes = bytes;
	}

	public byte[] getBytes() {
		return this.bytes;
	}

	public void setBytes(byte[] bytes) {
		this.bytes = bytes;
	}

	@Override
	public String toString() {
		return new String(this.bytes);
	}
}
