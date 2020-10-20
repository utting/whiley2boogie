// Copyright 2020 The Whiley Project Developers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package wy2boogie.util;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import wy2boogie.core.BoogieFile;
import wybs.lang.SyntacticException;
import wyfs.util.ArrayUtils;

/**
 * A wrapper for the "boogie" verifier.
 *
 * @author David J. Pearce
 *
 */
public class Boogie {
	private static final String BOOGIE_COMMAND = "boogie";

	private final String boogieCmd;

	/**
	 * Record command-line options.
	 */
	public final Map<String,String> options;

	public Boogie() {
		this(BOOGIE_COMMAND);
	}

	public Boogie(String command) {
		this.boogieCmd = command;
		this.options = new HashMap<>();
	}

	/**
	 * Control printing of enhanced error messages. If enabled then print Z3 error
	 * model enhanced error messages.
	 *
	 * @param flag
	 */
	public void setEnchancedErrorMessages(boolean flag) {
		options.put("enhancedErrorMessages", flag ? "1":"0");
	}

	/**
	 * Limit the number of seconds spent trying to verify each procedure
	 *
	 * @param seconds
	 */
	public void setTimeLimit(int seconds) {
		options.put("timeLimit", Integer.toString(seconds));
	}

	/**
	 * Check a given filename
	 *
	 * @param timeout (in milli seconds)
	 * @param boogie  Boogie contents (as a string)
	 * @return
	 */
	public Error[] check(int timeout, BoogieFile boogie) {
		String filename = null;
		try {
			// Determine id for the temporary file. This will help to identified should
			// there be a need during debugging.
			String id = boogie.getEntry().id().toString();
			// Create the temporary file.
			filename = createTemporaryFile(id, ".bpl", boogie.getBytes());
			// ===================================================
			// Construct command
			// ===================================================
			ArrayList<String> command = new ArrayList<>();
			command.add(boogieCmd);
			command.add("/nologo");
			// Add any registered command-line options
			for(Map.Entry<String,String> e : options.entrySet()) {
				String opt = e.getKey();
				String val = e.getValue();
				if(val == null) {
					command.add("/" + opt);
				} else {
					command.add("/" + opt + ":" + val);
				}
			}
			command.add(filename);
			// ===================================================
			// Construct the process
			// ===================================================
			ProcessBuilder builder = new ProcessBuilder(command);
			Process child = builder.start();
			try {
				// second, read the result whilst checking for a timeout
				InputStream input = child.getInputStream();
				InputStream error = child.getErrorStream();
				boolean success = child.waitFor(timeout, TimeUnit.MILLISECONDS);
				byte[] stdout = readInputStream(input);
				byte[] stderr = readInputStream(error);
				System.out.println("STDOUT: " + new String(stdout));
				System.out.println("STDERR: " + new String(stdout));
				if(success && child.exitValue() == 0) {
					return parseErrors(new String(stdout));
				}
			} finally {
				// make sure child process is destroyed.
				child.destroy();
			}
		} catch(IOException e) {
			throw new RuntimeException(e.getMessage(), e);
		} catch(InterruptedException e) {
			throw new RuntimeException(e.getMessage(),e);
		} finally {
			if(filename != null) {
				// delete the temporary file
				new File(filename).delete();
			}
		}
		return null;
	}

	public static class Error {
		private int line;
		private int column;
		private String message;

		public Error(int line, int col, String message) {
			this.line = line;
			this.column = col;
			this.message = message;
		}

		/**
		 * Get the line number of this error.
		 *
		 * @return
		 */
		public int getLine() {
			return line;
		}

		/**
		 * Get the column number within the given line where this error occurs.
		 *
		 * @return
		 */
		public int getColumn() {
			return column;
		}

		/**
		 * Get the error message.
		 * @return
		 */
		public String getMessage() {
			return message;
		}

		@Override
		public String toString() {
			return Integer.toString(line) + ":" + column + ":" + message;
		}
	}

	/**
	 * Parse Standard Output from Boogie into a useful form.
	 *
	 * @param output
	 * @return
	 */
	private static Error[] parseErrors(String output) {
		String[] lines = output.split("\n");
		Error[] errors = new Error[lines.length];
		for (int i = 0; i != lines.length; ++i) {
			// Decode boogie error line
			String ith = lines[i];
			if(ith.startsWith("Fatal Error:")) {
				errors[i] = new Error(0,0,ith);
				break;
			} else {
				int a = ith.indexOf('(');
				int b = ith.indexOf(',');
				int c = ith.indexOf(')');
				int d = ith.indexOf(':');
				if (a >= 0 && b >= 0 && c >= 0 && d >= 0) {
					int line = Integer.parseInt(ith.substring(a + 1, b));
					int col = Integer.parseInt(ith.substring(b + 1, c));
					String message = ith.substring(d + 1);
					errors[i] = new Error(line, col, message);
				}
			}
		}
		return ArrayUtils.removeAll(errors,null);
	}

	/**
	 * Write a given string into a temporary file which can then be checked by
	 * boogie.
	 *
	 * @param contents
	 * @return
	 */
	private static String createTemporaryFile(String prefix, String suffix, byte[] contents)
			throws IOException, InterruptedException {
		// Create new file
		File f = File.createTempFile(prefix, suffix);
		// Open for writing
		FileOutputStream fout = new FileOutputStream(f);
		// Write contents to file
		fout.write(contents);
		// Done creating file
		fout.close();
		//
		return f.getAbsolutePath();
	}


	/**
	 * Read an input stream entirely into a byte array.
	 *
	 * @param input
	 * @return
	 * @throws IOException
	 */
	private static byte[] readInputStream(InputStream input) throws IOException {
		byte[] buffer = new byte[1024];
		ByteArrayOutputStream output = new ByteArrayOutputStream();
		while (input.available() > 0) {
			int count = input.read(buffer);
			output.write(buffer, 0, count);
		}
		return output.toByteArray();
	}
}
