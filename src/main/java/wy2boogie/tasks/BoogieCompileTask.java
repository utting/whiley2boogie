package wy2boogie.tasks;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import java.util.function.Function;

import wy2boogie.core.BoogieFile;
import wy2boogie.translate.NotImplementedYet;
import wy2boogie.translate.Wyil2Boogie;
import wy2boogie.util.Boogie;
import wybs.lang.Build;
import wybs.lang.Build.Meter;
import wybs.util.AbstractBuildTask;
import wyfs.lang.Path;
import wyil.lang.WyilFile;

public class BoogieCompileTask extends AbstractBuildTask<WyilFile, BoogieFile> {
	/**
	 * Specify whether to print verbose progress messages or not
	 */
	private boolean verbose = true;

	/**
	 * Handle for the boogie verifier
	 */
	private Boogie verifier;

	/**
	 * Boogie process timeout (in milli-seconds)
	 */
	private int timeout = 10000;

	/**
	 * Specify whether verification enabled or not
	 */
	private boolean verification;

	/**
	 * Specify whether counterexample generation is enabled or not
	 */
	private boolean counterexamples;


	public BoogieCompileTask(Build.Project project, Path.Entry<BoogieFile> target, Path.Entry<WyilFile> source) {
		super(project, target, Arrays.asList(source));
		this.verifier = new Boogie();
	}

	public BoogieCompileTask setVerbose(boolean flag) {
		this.verbose = flag;
		return this;
	}

	public BoogieCompileTask setVerification(boolean flag) {
		this.verification = flag;
		return this;
	}

	public BoogieCompileTask setCounterExamples(boolean flag) {
		this.counterexamples = flag;
		return this;
	}

	@Override
	public Function<Meter,Boolean> initialise() throws IOException {
		// Extract target and source files for compilation. This is the component which
		// requires I/O.
		BoogieFile bf = target.read();
		WyilFile wyf = sources.get(0).read();
		// Construct the lambda for subsequent execution. This will eventually make its
		// way into some kind of execution pool, possibly for concurrent execution with
		// other tasks.
		return (Meter meter) -> execute(meter, bf, wyf);
	}

	/**
	 * The business end of a compilation task. The intention is that this
	 * computation can proceed without performing any blocking I/O. This means it
	 * can be used in e.g. a forkjoin task safely.
	 *
	 * @param target  --- The Boogie being written.
	 * @param sources --- The WyilFile(s) being translated.
	 * @return
	 */
	public boolean execute(Build.Meter meter, BoogieFile target, WyilFile source) {
		meter = meter.fork("BoogieCompiler");
		// Parse source files into target
		final ByteArrayOutputStream out = new ByteArrayOutputStream();
		final PrintWriter writer = new PrintWriter(out);
		// Write out the prelude
		writer.print(BOOGIE_PRELUDE);
		// Translate the WyilFile
		final Wyil2Boogie translator = new Wyil2Boogie(meter, writer);
		translator.setVerbose(verbose);
		translator.apply(source);
		// Done
		writer.close();
		target.setBytes(out.toByteArray());
		// Attempt to verify file with Boogie!
		if (verification) {
			Boogie.Error[] errors = verifier.check(timeout, target);
			if(verbose && errors != null) {
				// Debugging output
				for(int i=0;i!=errors.length;++i) {
					System.out.println(errors[i]);
				}
			}
			return errors != null && errors.length == 0;
		} else {
			return true;
		}
	}

	private static String BOOGIE_PRELUDE = "// The set of ALL Whiley values.\n" +
			"type WVal;\n" +
			"\n" +
			"type WField;      // field names for records and objects.\n" +
			"type WFuncName;   // names of functions\n" +
			"type WMethodName; // names of methods\n" +
			"type WRef;        // heap addresses\n" +
			"\n" +
			"// These typing predicates define various (disjoint) subsets of WVal.\n" +
			"// For null, there is just one WVal constant.\n" +
			"const unique null:WVal;\n" +
			"function isNull(v:WVal) returns (bool) { v == null }\n" +
			"function isInt(WVal) returns (bool);\n" +
			"function isBool(WVal) returns (bool);\n" +
			"function isArray(WVal) returns (bool);\n" +
			"function isRecord(WVal) returns (bool);\n" +
			"function isObject(WVal) returns (bool);   // Not used yet.\n" +
			"function isRef(WVal) returns (bool);\n" +
			"function isFunction(WVal) returns (bool); // means this is a function closure\n" +
			"function isMethod(WVal) returns (bool);   // means this is a method closure\n" +
			"\n" +
			"// byte is a subset of int.\n" +
			"function isByte(b:WVal) returns (bool) { isInt(b) && 0 <= toInt(b) && toInt(b) < 256 }\n" +
			"\n" +
			"// Now make sure these subsets of WVal are disjoint.\n" +
			"axiom (forall v:WVal :: isNull(v) ==>\n" +
			"         !isInt(v) && !isBool(v) && !isArray(v)\n" +
			"         && !isRecord(v) && !isObject(v) && !isRef(v) && !isFunction(v) && !isMethod(v));\n" +
			"axiom (forall v:WVal :: isInt(v) ==>\n" +
			"         !isNull(v) && !isBool(v) && !isArray(v)\n" +
			"         && !isRecord(v) && !isObject(v) && !isRef(v) && !isFunction(v) && !isMethod(v));\n" +
			"axiom (forall v:WVal :: isBool(v) ==>\n" +
			"         !isNull(v) && !isInt(v) && !isArray(v)\n" +
			"         && !isRecord(v) && !isObject(v) && !isRef(v) && !isFunction(v) && !isMethod(v));\n" +
			"axiom (forall v:WVal :: isArray(v) ==>\n" +
			"         !isNull(v) && !isInt(v) && !isBool(v)\n" +
			"         && !isRecord(v) && !isObject(v) && !isRef(v) && !isFunction(v) && !isMethod(v));\n" +
			"axiom (forall v:WVal :: isRecord(v) ==>\n" +
			"         !isNull(v) && !isInt(v) && !isBool(v)\n" +
			"         && !isArray(v) && !isObject(v) && !isRef(v) && !isFunction(v) && !isMethod(v));\n" +
			"axiom (forall v:WVal :: isObject(v) ==>\n" +
			"         !isNull(v) && !isInt(v) && !isBool(v)\n" +
			"         && !isArray(v) && !isRecord(v) && !isRef(v) && !isFunction(v) && !isMethod(v));\n" +
			"axiom (forall v:WVal :: isRef(v) ==>\n" +
			"         !isNull(v) && !isInt(v) && !isBool(v)\n" +
			"         && !isArray(v) && !isRecord(v) && !isObject(v) && !isFunction(v) && !isMethod(v));\n" +
			"axiom (forall v:WVal :: isFunction(v) ==>\n" +
			"         !isNull(v) && !isInt(v) && !isBool(v)\n" +
			"         && !isArray(v) && !isRecord(v) && !isObject(v) && !isRef(v) && !isMethod(v));\n" +
			"axiom (forall v:WVal :: isMethod(v) ==>\n" +
			"         !isNull(v) && !isInt(v) && !isBool(v)\n" +
			"         && !isArray(v) && !isRecord(v) && !isObject(v) && !isRef(v) && !isFunction(v));\n" +
			"\n" +
			"// int injection and extraction functions\n" +
			"function toInt(WVal) returns (int);\n" +
			"function fromInt(int) returns (WVal);\n" +
			"axiom (forall i:int :: isInt(fromInt(i)));\n" +
			"axiom (forall i:int :: toInt(fromInt(i)) == i);\n" +
			"axiom (forall v:WVal :: isInt(v) ==> fromInt(toInt(v)) == v);\n" +
			"\n" +
			"// bool injection and extraction functions\n" +
			"function toBool(WVal) returns (bool);\n" +
			"function fromBool(bool) returns (WVal);\n" +
			"axiom (forall b:bool :: isBool(fromBool(b)));\n" +
			"axiom (forall b:bool :: toBool(fromBool(b)) == b);\n" +
			"axiom (forall v:WVal :: isBool(v) ==> fromBool(toBool(v)) == v);\n" +
			"\n" +
			"// string injection and extraction functions\n" +
			"//type Unicode = int;\n" +
			"// const UnicodeMax int = 65536;\n" +
			"//function toString(WVal) returns ([int]Unicode);\n" +
			"//function strlen(WVal) returns (int);\n" +
			"//function fromString([int]Unicode,int) returns (WVal);\n" +
			"//axiom (forall s:[int]Unicode, len:int :: 0 <= len ==> isString(fromString(s,len)));\n" +
			"//axiom (forall s:[int]Unicode, len:int :: 0 <= len ==> toString(fromString(s,len)) == s);\n" +
			"//axiom (forall s:[int]Unicode, len:int :: 0 <= len ==> strlen(fromString(s,len)) == len);\n" +
			"//axiom (forall v:WVal :: isString(v) ==> fromString(toString(v), strlen(v)) == v);\n" +
			"//axiom (forall v:WVal :: isString(v) ==> strlen(v) >= 0);\n" +
			"\n" +
			"// general array injection and extraction functions\n" +
			"function toArray(WVal) returns ([int]WVal);\n" +
			"function arraylen(WVal) returns (int);\n" +
			"function fromArray([int]WVal,int) returns (WVal);\n" +
			"function arrayupdate(a:WVal, i:WVal, v:WVal) returns (WVal) {\n" +
			"    fromArray(toArray(a)[toInt(i) := v], arraylen(a)) }\n" +
			"axiom (forall s:[int]WVal, len:int :: 0 <= len ==> isArray(fromArray(s,len)));\n" +
			"// NOTE: 148 tests/valid programs fail without any array equality axiom:\n" +
			"// NOTE: this was wrong because should use arraylen(s), not len.\n" +
			"// axiom (forall s:[int]WVal, len:int :: 0 <= len ==> toArray(fromArray(s,len)) == s); // TOO STRONG\n" +
			"// alternative weaker pointwise equality axiom\n" +
			"// (this is sufficient to restore the 148 tests/valid. Only 2 programs have one more proof fail.)\n" +
			"axiom (forall s:[int]WVal, len:int, i:int :: 0 <= i && i < len\n" +
			"        ==> toArray(fromArray(s,len))[i] == s[i]);\n" +
			"axiom (forall s:[int]WVal, len:int :: 0 <= len ==> arraylen(fromArray(s,len)) == len);\n" +
			"axiom (forall v:WVal :: isArray(v) ==> fromArray(toArray(v), arraylen(v)) == v);\n" +
			"axiom (forall v:WVal :: isArray(v) ==> 0 <= arraylen(v));\n" +
			"\n" +
			"// Whiley array generators [val;len] are represented as:\n" +
			"//    fromArray(arrayconst(val), len)\n" +
			"// and an array literal like [val0, val1, val2] is constructed as:\n" +
			"//    fromArray(arrayconst(val0)[1 := val1][2 := val2], 2)\n" +
			"//\n" +
			"function arrayconst(val:WVal) returns ([int]WVal);\n" +
			"axiom (forall val:WVal, i:int :: arrayconst(val)[i] == val);\n" +
			"\n" +
			"// A few programs need extensionality of arrays.\n" +
			"// Boogie does not include this by default (page 12 KRML178).\n" +
			"// To avoid inconsistencies, we have just a very weak version of extensionality\n" +
			"// here, which is just enough to give extensionality on arrayupdate results.\n" +
			"// (If we required equality only in the domain of the array 0..len-1, this\n" +
			"//  would introduce an inconsistency with the above axioms:\n" +
			"//     a[0..100]==0 && a[101] == 1\n" +
			"//  && b[0..100]==0 && b[101] == 2\n" +
			"//  && wa = fromArray(a, 100)\n" +
			"//  && wb = fromArray(b, 100)\n" +
			"//  ==> wa == wb   // if we had a strong extensionality axiom, requiring only 0..100.\n" +
			"//   && wa != wb   // from a != b plus above axioms.\n" +
			"// )\n" +
			"axiom (forall a1:WVal, a2:WVal :: {isArray(a1),isArray(a2)}\n" +
			"    isArray(a1)\n" +
			"    && isArray(a2)\n" +
			"    ==>\n" +
			"       (arraylen(a1) == arraylen(a2)\n" +
			"        && (forall i:int :: 0 <= i && i < arraylen(a1) ==> toArray(a1)[i] == toArray(a2)[i])\n" +
			"       <==> a1 == a2)\n" +
			"    );\n" +
			"\n" +
			"\n" +
			"// Records (and objects)\n" +
			"// =====================\n" +
			"// These are similar to arrays, but indexed by WField constants.\n" +
			"// Undefined fields are all mapped to the 'undef__field' value.\n" +
			"//\n" +
			"// The Whiley type system distinguishes between record and objects\n" +
			"// (closed versus open), so this Boogie theory does not need to.\n" +
			"// Note that in this theory, two records being equal means they have the same set of fields\n" +
			"// (because all undefined fields are mapped to the non-Whiley value: undef__field).\n" +
			"\n" +
			"// Record and object injection and extraction functions\n" +
			"function toRecord(WVal) returns ([WField]WVal);\n" +
			"function fromRecord([WField]WVal) returns (WVal);\n" +
			"function recordupdate(a:WVal, f:WField, v:WVal) returns (WVal) {\n" +
			"    fromRecord(toRecord(a)[f := v]) }\n" +
			"axiom (forall s:[WField]WVal :: isRecord(fromRecord(s)));\n" +
			"axiom (forall s:[WField]WVal :: toRecord(fromRecord(s)) == s);\n" +
			"axiom (forall v:WVal :: isRecord(v) ==> fromRecord(toRecord(v)) == v);\n" +
			"\n" +
			"// Whiley record literals use empty__record[field1 := val1][field2 := val2] etc.\n" +
			"const unique empty__record : [WField]WVal;\n" +
			"const unique undef__field:WVal; // undefined fields map to this value\n" +
			"axiom (forall f:WField :: empty__record[f] == undef__field);\n" +
			"\n" +
			"axiom (forall a1:WVal, a2:WVal :: {isRecord(a1),isRecord(a2)}\n" +
			"    isRecord(a1)\n" +
			"    && isRecord(a2)\n" +
			"    ==>\n" +
			"       ((forall i:WField :: toRecord(a1)[i] == toRecord(a2)[i])\n" +
			"        <==> a1 == a2)\n" +
			"    );\n" +
			"\n" +
			"// bitwise operators (uninterpreted functions)\n" +
			"function byte_and(int, int) returns (int);\n" +
			"function byte_or(int, int) returns (int);\n" +
			"function byte_xor(int, int) returns (int);\n" +
			"function byte_shift_left(int, int) returns (int);\n" +
			"function byte_shift_right(int, int) returns (int);\n" +
			"function byte_invert(int) returns (int);\n" +
			"\n" +
			"function bitwise_and(int, int) returns (int);\n" +
			"function bitwise_or(int, int) returns (int);\n" +
			"function bitwise_xor(int, int) returns (int);\n" +
			"function bitwise_shift_left(int, int) returns (int);\n" +
			"function bitwise_shift_right(int, int) returns (int);\n" +
			"function bitwise_invert(int) returns (int);\n" +
			"\n" +
			"// typing axioms for the byte bitwise ops\n" +
			"axiom (forall b:int, i:int :: isByte(fromInt(byte_and(b,i))));\n" +
			"axiom (forall b:int, i:int :: isByte(fromInt(byte_or(b,i))));\n" +
			"axiom (forall b:int, i:int :: isByte(fromInt(byte_xor(b,i))));\n" +
			"axiom (forall b:int, i:int :: isByte(fromInt(byte_shift_left(b,i))));\n" +
			"axiom (forall b:int, i:int :: isByte(fromInt(byte_shift_right(b,i))));\n" +
			"axiom (forall b:int :: isByte(fromInt(byte_invert(b))));\n" +
			"\n" +
			"// New and dereferencing (uninterpreted functions)\n" +
			"function toRef(WVal) returns (WRef);\n" +
			"function fromRef(WRef) returns (WVal);\n" +
			"axiom (forall r:WRef :: isRef(fromRef(r)));\n" +
			"axiom (forall r:WRef :: toRef(fromRef(r)) == r);\n" +
			"axiom (forall v:WVal :: isRef(v) ==> fromRef(toRef(v)) == v);\n" +
			"// this chooses a fresh (unallocated) reference.\n" +
			"function new([WRef]bool) returns (WRef);\n" +
			"axiom (forall m : [WRef]bool :: ! m[new(m)]);  \n" +
			"\n" +
			"\n" +
			"// Higher-order functions are stored as Closure values\n" +
			"// Lambda functions take only one capture value for now.\n" +
			"type FunctionClosure;\n" +
			"function toFunction(WVal) returns (FunctionClosure);\n" +
			"function fromFunction(FunctionClosure) returns (WVal);\n" +
			"axiom (forall f:FunctionClosure :: isFunction(fromFunction(f)));\n" +
			"axiom (forall f:FunctionClosure :: toFunction(fromFunction(f)) == f);\n" +
			"axiom (forall v:WVal :: isFunction(v) ==> fromFunction(toFunction(v)) == v);\n" +
			"\n" +
			"\n" +
			"function closure__0(f:WFuncName) returns (FunctionClosure);\n" +
			"function closure__1(f:WFuncName, v1:WVal) returns (FunctionClosure);\n" +
			"function closure__2(f:WFuncName, v1:WVal, v2:WVal) returns (FunctionClosure);\n" +
			"function closure__3(f:WFuncName, v1:WVal, v2:WVal, v3:WVal) returns (FunctionClosure);\n" +
			"function apply__0(FunctionClosure) returns (WVal);\n" +
			"function apply__1(FunctionClosure, WVal) returns (WVal);\n" +
			"function apply__2(FunctionClosure, WVal, WVal) returns (WVal);\n" +
			"function apply__3(FunctionClosure, WVal, WVal, WVal) returns (WVal);\n" +
			"//\n" +
			"// Then for each lambda func &(x->E(x,y)):\n" +
			"// 1. we give it a unique name, say func__f:\n" +
			"//    const unique func__f:WFuncName;\n" +
			"// 2. we generate a global function, say f, that takes the local and global inputs:\n" +
			"//    function f(y:WVal, x:WVal) returns (result:WVal) { E(x,y) }\n" +
			"// 3. we generate an apply axiom for that function:\n" +
			"//    axiom (forall v1:WVal, v2:WVal ::\n" +
			"//      apply__1(closure__1(func__f, v1), v2) == f(v1, v2));\n" +
			"\n" +
			"\n" +
			"\n" +
			"// TYPE TEMPLATES SUPPORT\n" +
			"\n" +
			"type WType;       // typing properties\n" +
			"function is__type(p:WType, v:WVal) returns (bool);\n" +
			"\n" +
			"// properties for primitive types\n" +
			"const unique type__int:WType;\n" +
			"const unique type__byte:WType;\n" +
			"const unique type__bool:WType;\n" +
			"const unique type__null:WType;\n" +
			"\n" +
			"axiom (forall val:WVal :: is__type(type__int, val) <==> isInt(val));\n" +
			"axiom (forall val:WVal :: is__type(type__byte, val) <==> isByte(val));\n" +
			"axiom (forall val:WVal :: is__type(type__bool, val) <==> isBool(val));\n" +
			"axiom (forall val:WVal :: is__type(type__null, val) <==> isNull(val));\n";
}
