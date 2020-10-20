type fun_t<S,T> is function(S)->(T)

function combinator<A,B,C>(fun_t<A,B> f1, fun_t<B,C> f2) -> fun_t<A,C>:
    return &(A a -> f2(f1(a)))

public function inc(int x) -> (int y):
    return x + 1

public function floor(int x) -> (int|null y):
    if x >= 0:
        return x
    else:
        return null

public export method test():
    // Setup the combinator
    fun_t<int,int|null> f = combinator(&inc,&floor)
    // now test it
    assume f(1) == 2
    assume f(0) == 1
    assume f(-1) == 0
    assume f(-2) == null