public export method test():
    int x = 0
    int y = 0
    //
    x, y = 1,x
    //
    assert x == 1
    assert y == 0
    
