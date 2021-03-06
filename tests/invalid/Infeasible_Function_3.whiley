// Similar to Infeasible_Function_2, but recursive with a call that makes no progress.
// This function is infeasible when a==1.
// So we must prove feasibility before using axioms about the function results.

function f(int a) -> (int r)
requires 0 < a
requires a <= 2
ensures (2 * r) == a:
    //
    int b = f(a)
    return b
