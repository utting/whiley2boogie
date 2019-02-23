var w__heap:[WRef]WVal;
var w__alloc:[WRef]bool;

//DEBUG: resolving compilation unit ConstrainedList_Valid_8
//DEBUG: generating compilation unit ConstrainedList_Valid_8
function is_nat(x:WVal) returns (bool) {
    isInt(x) &&
      toInt(x) >= 0 }

function ConstrainedList_Valid_8__update__pre(list:WVal, index:WVal, value:WVal) returns (bool)
{
      isArray(list) && (forall i__1:int :: 0 <= i__1 && i__1 < arraylen(list) ==> is_nat(toArray(list)[i__1])) &&
      is_nat(index) &&
      is_nat(value) &&
      toInt(index) < arraylen(list)
}
function ConstrainedList_Valid_8__update(list:WVal, index:WVal, value:WVal) returns (rs:WVal);
axiom (forall list:WVal, index:WVal, value:WVal :: {ConstrainedList_Valid_8__update(list, index, value)}
    ConstrainedList_Valid_8__update__pre(list, index, value)
    ==> (exists rs:WVal ::
        ConstrainedList_Valid_8__update(list, index, value) == (rs) &&
        isArray(rs) && (forall i__2:int :: 0 <= i__2 && i__2 < arraylen(rs) ==> is_nat(toArray(rs)[i__2])) &&
      fromInt(arraylen(rs)) == fromInt(arraylen(list))));

procedure ConstrainedList_Valid_8__update__impl(list:WVal, index:WVal, value:WVal) returns (rs:WVal);
    requires ConstrainedList_Valid_8__update__pre(list, index, value);
    ensures isArray(rs) && (forall i__3:int :: 0 <= i__3 && i__3 < arraylen(rs) ==> is_nat(toArray(rs)[i__3]));
    ensures fromInt(arraylen(rs)) == fromInt(arraylen(list));
implementation ConstrainedList_Valid_8__update__impl(list__0:WVal, index:WVal, value:WVal) returns (rs:WVal)
{
    var list : WVal where isArray(list) && (forall i__4:int :: 0 <= i__4 && i__4 < arraylen(list) ==> is_nat(toArray(list)[i__4]));
    list := list__0;
    assert 0 <= toInt(index) && toInt(index) < arraylen(list);
    list := fromArray(toArray(list)[toInt(index) := value], arraylen(list));
    rs := list;
    return;
}

function ConstrainedList_Valid_8__test__pre() returns (bool)
{
      true
}
procedure ConstrainedList_Valid_8__test();
    modifies w__heap, w__alloc;
    requires ConstrainedList_Valid_8__test__pre();
implementation ConstrainedList_Valid_8__test()
{
    var xs : WVal where isArray(xs) && (forall i__5:int :: 0 <= i__5 && i__5 < arraylen(xs) ==> is_nat(toArray(xs)[i__5]));
    xs := fromArray(arrayconst(fromInt(1))[1 := fromInt(2)][2 := fromInt(3)][3 := fromInt(4)], 4);
    assert ConstrainedList_Valid_8__update__pre(xs, fromInt(0), fromInt(10));
    xs := ConstrainedList_Valid_8__update(xs, fromInt(0), fromInt(10));
    assert ConstrainedList_Valid_8__update__pre(xs, fromInt(3), fromInt(15));
    xs := ConstrainedList_Valid_8__update(xs, fromInt(3), fromInt(15));
    assert xs == fromArray(arrayconst(fromInt(10))[1 := fromInt(2)][2 := fromInt(3)][3 := fromInt(15)], 4);
}

