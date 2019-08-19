const Context__Height:int;
var w__heap:[WRef]WVal;
var w__alloc:[WRef]bool;

function tmp__f__pre(a:WVal) returns (bool)
{
      isInt(a) &&
      0 < toInt(a) &&
      toInt(a) <= 2
}
function tmp__f__post(a:WVal, r:WVal) returns (bool)
{
    isInt(r) &&
      fromInt(2 * toInt(r)) == a
}
function tmp__f(a:WVal) returns (r:WVal);

// NOTE: we change the trigger of this to f__pre so that it is available inside the function.
axiom (forall i:WVal :: {tmp__f__pre(i)} tmp__f__pre(i) ==> tmp__f__post(i, tmp__f(i)));

procedure tmp__f__impl(a:WVal) returns (r:WVal);
    free requires Context__Height > 1;
    requires tmp__f__pre(a);
    ensures tmp__f__post(a, r);
implementation tmp__f__impl(a:WVal) returns (r:WVal)
{
    // assert tmp__f__pre(fromInt(1));
    // assert tmp__f(fromInt(1)) != fromInt( toInt( tmp__f(fromInt(1))) + 1 );
    r := fromInt(1);
    return;
}

