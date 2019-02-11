method Max(a: int, b: int) returns (c: int)
  ensures a <= c && b <= c && (a == c || b == c)
{
  if a > b {
    c := a;
  } else {
    c := b;
  }
}

method Test()
{
   var m := Max(3, 5);
   var n := Max(-3, -5);

   assert m == 5;
   assert n == -3;
}
