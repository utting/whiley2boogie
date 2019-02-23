property P(int i) where i > 0
property Q(int i, int o) where i+o == 10

function f(int i) -> (int o)
requires P(i)
ensures Q(i,o):
    return 10 - i
