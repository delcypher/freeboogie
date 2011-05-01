type T;

procedure indexOf(x : T, a : [int] T, al : int) returns (i : int) {
  i := 0;
  while (i < al && a[i] != x) { i := i + 1; }
}
