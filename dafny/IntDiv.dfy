method IntDiv (m : int, n : int) returns (d : int, r : int)
    requires n > 0
    ensures m == d * n + r
    ensures 0 <= r && r < n
{
    d := m / n;
    r := m % n;
}