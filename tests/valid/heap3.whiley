method test() -> (&int[] r)
ensures |*r| == 3
ensures *r[1] == 12:
    &int[] aa = new [1,3,5]
    &int[] bb = new [10,11,12,13]
    (*aa)[1] = (*bb)[2]
    assert *aa[0] == 1
    assert *aa[1] == 12
    assert *aa[2] == 5
    return aa
