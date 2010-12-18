axiom (forall x : int :: x % 2 == 0 || (x + 1) % 2 == 0);

// Break with label.
procedure p(x : int) returns(y : int) 
  ensures y % 2 == 0;
{
  y := x;
entry:
  if (true) {
    if (y % 2 == 0) { break entry; }
    y := x + 1;
  }
}
