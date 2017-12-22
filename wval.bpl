
// The set of ALL Whiley values.
type WVal;

type WField;      // field names for records and objects.
type WFuncName;   // names of functions
type WMethodName; // names of methods
type WRef;        // heap addresses

// These typing predicates define various (disjoint) subsets of WVal.
// For null, there is just one WVal constant.
const unique null:WVal;
function isNull(v:WVal) returns (bool) { v == null }
function isInt(WVal) returns (bool);
function isBool(WVal) returns (bool);
function isArray(WVal) returns (bool);
function isRecord(WVal) returns (bool);
function isObject(WVal) returns (bool);   // Not used yet.
function isRef(WVal) returns (bool);      // TODO how to represent these?
function isFunction(WVal) returns (bool); // means this is a function closure
function isMethod(WVal) returns (bool);   // means this is a method closure

// byte is a subset of int.
function isByte(b:WVal) returns (bool) { isInt(b) && 0 <= toInt(b) && toInt(b) < 256 }

// Now make sure these subsets of WVal are disjoint.
axiom (forall v:WVal :: isNull(v) ==>
         !isInt(v) && !isBool(v) && !isArray(v)
         && !isRecord(v) && !isObject(v) && !isRef(v) && !isFunction(v) && !isMethod(v));
axiom (forall v:WVal :: isInt(v) ==>
         !isNull(v) && !isBool(v) && !isArray(v)
         && !isRecord(v) && !isObject(v) && !isRef(v) && !isFunction(v) && !isMethod(v));
axiom (forall v:WVal :: isBool(v) ==>
         !isNull(v) && !isInt(v) && !isArray(v)
         && !isRecord(v) && !isObject(v) && !isRef(v) && !isFunction(v) && !isMethod(v));
axiom (forall v:WVal :: isArray(v) ==>
         !isNull(v) && !isInt(v) && !isBool(v)
         && !isRecord(v) && !isObject(v) && !isRef(v) && !isFunction(v) && !isMethod(v));
axiom (forall v:WVal :: isRecord(v) ==>
         !isNull(v) && !isInt(v) && !isBool(v)
         && !isArray(v) && !isObject(v) && !isRef(v) && !isFunction(v) && !isMethod(v));
axiom (forall v:WVal :: isObject(v) ==>
         !isNull(v) && !isInt(v) && !isBool(v)
         && !isArray(v) && !isRecord(v) && !isRef(v) && !isFunction(v) && !isMethod(v));
axiom (forall v:WVal :: isRef(v) ==>
         !isNull(v) && !isInt(v) && !isBool(v)
         && !isArray(v) && !isRecord(v) && !isObject(v) && !isFunction(v) && !isMethod(v));
axiom (forall v:WVal :: isFunction(v) ==>
         !isNull(v) && !isInt(v) && !isBool(v)
         && !isArray(v) && !isRecord(v) && !isObject(v) && !isRef(v) && !isMethod(v));
axiom (forall v:WVal :: isMethod(v) ==>
         !isNull(v) && !isInt(v) && !isBool(v)
         && !isArray(v) && !isRecord(v) && !isObject(v) && !isRef(v) && !isFunction(v));

// int injection and extraction functions
function toInt(WVal) returns (int);
function fromInt(int) returns (WVal);
axiom (forall i:int :: isInt(fromInt(i)));
axiom (forall i:int :: toInt(fromInt(i)) == i);
axiom (forall v:WVal :: isInt(v) ==> fromInt(toInt(v)) == v);

// bool injection and extraction functions
function toBool(WVal) returns (bool);
function fromBool(bool) returns (WVal);
axiom (forall b:bool :: isBool(fromBool(b)));
axiom (forall b:bool :: toBool(fromBool(b)) == b);
axiom (forall v:WVal :: isBool(v) ==> fromBool(toBool(v)) == v);

// string injection and extraction functions
//type Unicode = int;
// const UnicodeMax int = 65536;
//function toString(WVal) returns ([int]Unicode);
//function strlen(WVal) returns (int);
//function fromString([int]Unicode,int) returns (WVal);
//axiom (forall s:[int]Unicode, len:int :: 0 <= len ==> isString(fromString(s,len)));
//axiom (forall s:[int]Unicode, len:int :: 0 <= len ==> toString(fromString(s,len)) == s);
//axiom (forall s:[int]Unicode, len:int :: 0 <= len ==> strlen(fromString(s,len)) == len);
//axiom (forall v:WVal :: isString(v) ==> fromString(toString(v), strlen(v)) == v);
//axiom (forall v:WVal :: isString(v) ==> strlen(v) >= 0);

// general array injection and extraction functions
function toArray(WVal) returns ([int]WVal);
function arraylen(WVal) returns (int);
function fromArray([int]WVal,int) returns (WVal);
function arrayupdate(a:WVal, i:WVal, v:WVal) returns (WVal) {
    fromArray(toArray(a)[toInt(i) := v], arraylen(a)) }
axiom (forall s:[int]WVal, len:int :: 0 <= len ==> isArray(fromArray(s,len)));
// NOTE: 148 tests/valid programs fail without any array equality axiom:
// NOTE: this was wrong because should use arraylen(s), not len.
// axiom (forall s:[int]WVal, len:int :: 0 <= len ==> toArray(fromArray(s,len)) == s); // TOO STRONG
// alternative weaker pointwise equality axiom
// (this is sufficient to restore the 148 tests/valid. Only 2 programs have one more proof fail.)
axiom (forall s:[int]WVal, len:int, i:int :: 0 <= i && i < len
        ==> toArray(fromArray(s,len))[i] == s[i]);
axiom (forall s:[int]WVal, len:int :: 0 <= len ==> arraylen(fromArray(s,len)) == len);
axiom (forall v:WVal :: isArray(v) ==> fromArray(toArray(v), arraylen(v)) == v);
axiom (forall v:WVal :: isArray(v) ==> 0 <= arraylen(v));

// Whiley array generators [val;len] are represented as:
//    fromArray(arrayconst(val), len)
// and an array literal like [val0, val1, val2] is constructed as:
//    fromArray(arrayconst(val0)[1 := val1][2 := val2], 2)
//
function arrayconst(val:WVal) returns ([int]WVal);
axiom (forall val:WVal, i:int :: arrayconst(val)[i] == val);

// A few programs need extensionality of arrays.
// Boogie does not include this by default (page 12 KRML178).
// To avoid inconsistencies, we have just a very weak version of extensionality
// here, which is just enough to give extensionality on arrayupdate results.
// (If we required equality only in the domain of the array 0..len-1, this
//  would introduce an inconsistency with the above axioms:
//     a[0..100]==0 && a[101] == 1
//  && b[0..100]==0 && b[101] == 2
//  && wa = fromArray(a, 100)
//  && wb = fromArray(b, 100)
//  ==> wa == wb   // if we had a strong extensionality axiom, requiring only 0..100.
//   && wa != wb   // from a != b plus above axioms.
// )
axiom (forall a1:WVal, a2:WVal :: {isArray(a1),isArray(a2)}
    isArray(a1)
    && isArray(a2)
    ==>
       (arraylen(a1) == arraylen(a2)
        && (forall i:int :: 0 <= i && i < arraylen(a1) ==> toArray(a1)[i] == toArray(a2)[i])
       <==> a1 == a2)
    );


// Records (and objects)
// =====================
// These are similar to arrays, but indexed by WField constants.
// Undefined fields are all mapped to the 'undef__field' value.
//
// The Whiley type system distinguishes between record and objects
// (closed versus open), so this Boogie theory does not need to.
// Note that in this theory, two records being equal means they have the same set of fields
// (because all undefined fields are mapped to the non-Whiley value: undef__field).

// Record and object injection and extraction functions
function toRecord(WVal) returns ([WField]WVal);
function fromRecord([WField]WVal) returns (WVal);
function recordupdate(a:WVal, f:WField, v:WVal) returns (WVal) {
    fromRecord(toRecord(a)[f := v]) }
axiom (forall s:[WField]WVal :: isRecord(fromRecord(s)));
axiom (forall s:[WField]WVal :: toRecord(fromRecord(s)) == s);
axiom (forall v:WVal :: isRecord(v) ==> fromRecord(toRecord(v)) == v);

// Whiley record literals use empty__record[field1 := val1][field2 := val2] etc.
const unique empty__record : [WField]WVal;
const unique undef__field:WVal; // undefined fields map to this value
axiom (forall f:WField :: empty__record[f] == undef__field);

axiom (forall a1:WVal, a2:WVal :: {isRecord(a1),isRecord(a2)}
    isRecord(a1)
    && isRecord(a2)
    ==>
       ((forall i:WField :: toRecord(a1)[i] == toRecord(a2)[i])
        <==> a1 == a2)
    );

// bitwise operators (uninterpreted functions)
function byte_and(int, int) returns (int);
function byte_or(int, int) returns (int);
function byte_xor(int, int) returns (int);
function byte_shift_left(int, int) returns (int);
function byte_shift_right(int, int) returns (int);
function byte_invert(int) returns (int);

function bitwise_and(int, int) returns (int);
function bitwise_or(int, int) returns (int);
function bitwise_xor(int, int) returns (int);
function bitwise_shift_left(int, int) returns (int);
function bitwise_shift_right(int, int) returns (int);
function bitwise_invert(int) returns (int);

// typing axioms for the byte bitwise ops
axiom (forall b:int, i:int :: isByte(fromInt(byte_and(b,i))));
axiom (forall b:int, i:int :: isByte(fromInt(byte_or(b,i))));
axiom (forall b:int, i:int :: isByte(fromInt(byte_xor(b,i))));
axiom (forall b:int, i:int :: isByte(fromInt(byte_shift_left(b,i))));
axiom (forall b:int, i:int :: isByte(fromInt(byte_shift_right(b,i))));
axiom (forall b:int :: isByte(fromInt(byte_invert(b))));

// New and dereferencing (uninterpreted functions)
function toRef(WVal) returns (WRef);
function fromRef(WRef) returns (WVal);
axiom (forall r:WRef :: isRef(fromRef(r)));
axiom (forall r:WRef :: toRef(fromRef(r)) == r);
axiom (forall v:WVal :: isRef(v) ==> fromRef(toRef(v)) == v);
// this chooses a fresh (unallocated) reference.
function new([WRef]bool) returns (WRef);
axiom (forall m : [WRef]bool :: ! m[new(m)]);  


// Higher-order functions are stored as Closure values
// Lambda functions take only one capture value for now.
type FunctionClosure;
function toFunction(WVal) returns (FunctionClosure);
function fromFunction(FunctionClosure) returns (WVal);
axiom (forall f:FunctionClosure :: isFunction(fromFunction(f)));
axiom (forall f:FunctionClosure :: toFunction(fromFunction(f)) == f);
axiom (forall v:WVal :: isFunction(v) ==> fromFunction(toFunction(v)) == v);


function closure__0(f:WFuncName) returns (FunctionClosure);
function closure__1(f:WFuncName, v1:WVal) returns (FunctionClosure);
function closure__2(f:WFuncName, v1:WVal, v2:WVal) returns (FunctionClosure);
function closure__3(f:WFuncName, v1:WVal, v2:WVal, v3:WVal) returns (FunctionClosure);
function apply__0(FunctionClosure) returns (WVal);
function apply__1(FunctionClosure, WVal) returns (WVal);
function apply__2(FunctionClosure, WVal, WVal) returns (WVal);
function apply__3(FunctionClosure, WVal, WVal, WVal) returns (WVal);
//
// Then for each lambda func &(x->E(x,y)):
// 1. we give it a unique name, say func__f:
//    const unique func__f:WFuncName;
// 2. we generate a global function, say f, that takes the local and global inputs:
//    function f(y:WVal, x:WVal) returns (result:WVal) { E(x,y) }
// 3. we generate an apply axiom for that function:
//    axiom (forall v1:WVal, v2:WVal ::
//      apply__1(closure__1(func__f, v1), v2) == f(v1, v2));
