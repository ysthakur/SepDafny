method LoopToZero(m : int, p : int) returns (x: int, z: int)
  requires m > 0
  ensures z == p - m
{
  x := m;
  z := p;
  while x > 0
    invariant x >=0 && z - x == p - m
  {
    z := z - 1;
    x := x - 1;
  }
}