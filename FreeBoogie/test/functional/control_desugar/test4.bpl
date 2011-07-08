axiom (forall x : int :: x % 2 == 0 || (x + 1) % 2 == 0);
axiom (forall x : int :: x % 2 == 0 || x % 2 == 1);

// Varied breaks.
procedure p(x : int) returns(y : int) 
  ensures y % 2 == 0;
{
  goto A, B;
A:
  while (x % 2 == 1) {
    x := x + 1;
    break;
  }
  goto done;
B:
  while (x % 2 == 1) {
    while (x % 2 == 1) {
      x := x + 1;
      if (x % 2 == 0) {
        break B;
      }
    }
  }
done:
  y := x;
}
