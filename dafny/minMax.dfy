method MinMax (x : int, y : int) returns (min : int, max : int)
    ensures min <= x && min <= y && (min == x || min == y)
    ensures max >= x && max >= y && (max == x || max == y)     
{
    if (x < y) {
        min := x;
        max := y;
    }
    else {
        max := x;
        min := y;
    }
}
