type nat is (int x) where x >= 0

function update(nat[] list, nat index, nat value) -> (nat[] rs)
requires index < |list|
ensures |rs| == |list|:
    list[index] = value
    return list

public export method test() :
    nat[] xs = [1, 2, 3, 4]
    xs = update(xs, 0, 10)
    xs = update(xs, 3, 15)
    assert xs == [10, 2, 3, 15]

