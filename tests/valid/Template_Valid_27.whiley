method f<T>(&int x, T y) -> (int r):
    //
    return *x

public method get(int v, &int y) -> (int r):
    //
    &int x = new (6)
    //
    return f<int>(x,2) + f<int>(y,3)

public export method test():
    //
    &int p = new (123)
    //
    int v = get(2,p)
    //
    assume v == 129
