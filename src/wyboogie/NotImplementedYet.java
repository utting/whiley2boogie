package wyboogie;

import wycc.lang.Attribute.Source;
import wyil.lang.SyntaxTree.Location;

/**
 * Not Implemented errors, with some context information.
 *
 * @author Mark Utting
 */
@SuppressWarnings("serial")
public class NotImplementedYet extends RuntimeException {
	protected Location<?> location;

	/**
	 * Record a Not Implemented Yet message, with a source file location.
	 *
	 * @param message
	 * @param loc can be null if not known.
	 */
	public NotImplementedYet(String message, Location<?> loc) {
		super(message);
		location = loc;
	}

	public NotImplementedYet(Throwable cause, Location<?> loc) {
		super(cause);
		location = loc;
	}

	public NotImplementedYet(String message, Throwable cause, Location<?> loc) {
		super(message, cause);
		location = loc;
	}

	public NotImplementedYet(String message, Throwable cause, Location<?> loc, boolean enableSuppression, boolean writableStackTrace) {
		super(message, cause, enableSuppression, writableStackTrace);
		location = loc;
	}

	@Override
	public String getMessage() {
		String msg = super.getMessage();
		Source src = null;
		if (location != null) {
			src = location.attribute(Source.class);
			if (src == null) {
				src = location.getEnclosingTree().getEnclosingDeclaration().attribute(Source.class);
			}
		}
		if (src == null) {
			return msg + " in " + location.toString();
		} else {
			return msg + " at " + src.toString();
		}
	}
}
