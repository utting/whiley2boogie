property P(int i) where i > 0
property Q(int i, int o) where i+o == 10

method m(int i) -> (int o)
requires P(i)
ensures Q(i,o):
    return 10 - i

method m2():
    int x = 1
    int y = m(x)
    assert x + y == 10
