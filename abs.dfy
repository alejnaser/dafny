method Abs(x: int) returns (y: int)
   ensures 0 <= y
   ensures 0 <= x ==> x == y
   ensures 0 > x ==> -x == y
{
   if x < 0
      { return -x; }
   else
      { return x; }
}

method Test()
{
   var v := Abs(3);
   assert 0 <= v;
   assert v == 3;

   var w := Abs(-5);
   assert 0 <= w;
   assert w == 5;
}
