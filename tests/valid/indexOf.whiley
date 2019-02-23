type nat is (int n) where n >= 0

function indexOf(int[] items, int item) -> (int|null r)
// If valid index returned, element at r matches item
ensures r is int ==> items[r] == item
// If invalid index return, no element matches item
ensures r is null ==> all{i in 0..|items| | items[i] != item}:
    //
    nat i = 0
    while i < |items|
        where all { k in 0 .. i | items[k] != item }:
        //    
        if items[i] == item:
            return i
        i = i + 1
    //
    return null
