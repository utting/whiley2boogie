type Proc is &{int data}

type Func is {
    function reader(int)->int
}

function test(Func f, int arg) -> int:
    return f.read(arg)
