type pos is (int x) where x >= 0
type neg is (int x) where x < 0

type R1 is { pos|neg f }

function f() -> (R1 r):
    return {f:0}