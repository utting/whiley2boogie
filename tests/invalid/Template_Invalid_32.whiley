type fun_t<T> is function({T f})->(int)

function bigger(fun_t<int> fn) -> fun_t<int|bool>:
    return fn

function bigger2(fun_t<int> fn) -> function({int|bool f})->(int):
    return fn

function smaller(fun_t<int|bool> fn) -> fun_t<int>:
    return fn

function bigger2(fun_t<int|bool> fn) -> function({int f})->(int):
    return fn