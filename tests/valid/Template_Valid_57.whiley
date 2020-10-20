function f<T>() -> function(T)->({T f}):
    return &(T x -> {f:x})

function apply<T>(T x, function(T)->({T f}) fn) -> T:
    return fn(x).f

public export method test():
    // Creates a "positive" constraint cycle
    int x = apply(1,f())
    //
    assume x == 1