axiom (forall x : int :: x % 2 == 0 || (x + 1) % 2 == 0);

// Test the desugaring of if.
procedure p(x : int) returns(y : int) 
  ensures y % 2 == 0;
{
  if (x % 2 == 0) {
    y := x;
  } else {
    y := x + 1;
  }
}
