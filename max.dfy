method Max(a: int, b: int) returns (c: int)
ensures a <= c && b <= c && (a == c || b == c)
{
  if a > b {
    c := a;
  } else {
    c := b;
  }
}
