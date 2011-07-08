axiom (forall x : int :: x % 2 == 0 || (x + 1) % 2 == 0);

// The 'if' statement is labeled.
procedure p(x : int) returns(y : int)
  ensures y % 2 == 0;
{
  goto a, b;
  assert false;

a:b:
  if (x % 2 == 0) {
    y := x;
  } else {
    y := x + 1;
  }
}
