axiom (forall x : int :: x % 2 == 0 || (x + 1) % 2 == 0);

// Nested 'if's.
procedure p(x : int) returns(y : int) 
  ensures y % 2 == 0;
{
  if (x % 2 == 0) {
    y := x;
  } else if (x % 2 == 1) {
    y := x + 1;
  } else {
    if (x % 2 != 0) {
      y := x + 1;
    } else {
      y := x;
    }
  }
}
