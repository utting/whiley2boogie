package wy2boogie.translate;

import wybs.lang.SyntacticItem;
import wybs.util.AbstractCompilationUnit.Attribute;
import wyc.lang.WhileyFile;

/**
 * Not Implemented errors, with some context information.
 *
 * TODO: add the file name?
 *
 * @author Mark Utting
 */
@SuppressWarnings("serial")
public class NotImplementedYet extends RuntimeException {
	protected SyntacticItem location;

	/**
	 * Record a Not Implemented Yet message, with a source file location.
	 *
	 * @param message
	 * @param loc can be null if not known.
	 */
	public NotImplementedYet(String message, SyntacticItem loc) {
		super(message);
		location = loc;
	}

	public NotImplementedYet(Throwable cause, SyntacticItem loc) {
		super(cause);
		location = loc;
	}

	public NotImplementedYet(String message, Throwable cause, SyntacticItem loc) {
		super(message, cause);
		location = loc;
	}

	public NotImplementedYet(String message, Throwable cause, SyntacticItem loc, boolean enableSuppression, boolean writableStackTrace) {
		super(message, cause, enableSuppression, writableStackTrace);
		location = loc;
	}

	@Override
	public String getMessage() {
		String msg = super.getMessage();
		String context = "";
		Attribute.Span src = null;
		if (location != null) {
		    context = " isType " + location.toString();
			src = location.getParent(Attribute.Span.class);
			if (src != null) {
				// FIXME: need to determine the line number here somehow --djp
			    context = " at (" + src.getStart() + ".." + src.getEnd() + ")";
			}
		}
		return msg + context;
	}
}
