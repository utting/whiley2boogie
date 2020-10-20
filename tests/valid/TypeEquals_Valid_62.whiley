// Example from #936
type Point is {int x, int y}
type Location is {int x, int y}

function toLocation(Point|Location pl) -> (Location r):
    if pl is Point:
        return Location{x:0,y:0}
    else: 
        return pl

public export method test():
    Point p = {x:1, y:2}
    Location l1 = {x:1, y:2}    
    Location l2 = {x:100, y:2033}
    //
    assume toLocation(p) == {x:0,y:0}
    assume toLocation(l1) == l1
    assume toLocation(l2) == {x:100,y:2033}