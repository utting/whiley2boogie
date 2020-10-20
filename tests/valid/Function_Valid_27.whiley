function init() -> (int r)
ensures r == 1:
    return 1

function init() -> (bool r)
ensures r == false:
    return false

function init() -> (int[] r)
ensures r == []:
    return []

public export method test():
    int i = init()
    bool j = init()
    int[] k = init()
    //
    assert i == 1
    assert j == false
    assert k == []
    
