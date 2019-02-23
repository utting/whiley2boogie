method test():
    &int aa = new 3
    &int bb = new 4
    assert *bb == *aa + 1
    *aa = *bb * 2
    assert *bb == 4 && *aa == 8

