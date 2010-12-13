procedure P(a : [int]int, x : int) returns (i : int) {
    i := 0;
  head:
    goto body, after;
  body:
    assume a[i] != x;
    i := i + 1;
    goto head;
  after:
    assume a[i] == x;
}
