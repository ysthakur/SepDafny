method Square (x : int) returns (z : int) 
  requires x > 0 
  ensures z == x * x
{
    var y : int := 0;
    z := 0;
    while y < x 
      invariant y <= x && z == y * x
    {
      z := z + x;
      y := y + 1;
    }
}
