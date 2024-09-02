method TwoLoops(a : int, b : int, c : int) returns (x:int, y :int, z :int)
  requires a > 0 && b > 0 && c > 0
  ensures z == a + b + c
{
     x := 0;
     y := 0;
     z := c;
     while x < a
      invariant x <= a && y == 0 && z == x + y + c
     {
       x := x + 1;
       z := z + 1;
     }
     while y < b 
      invariant y <= b && x == a && z == a + y + c
     {
       y := y + 1;
       z := z + 1;
     }
}