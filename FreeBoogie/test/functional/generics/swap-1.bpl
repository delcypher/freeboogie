type Ref;
type Name x;
var heap : <x>[Ref, Name x]x;

procedure swap<x>(o : Ref, a : Name x, b : Name x) {
  var tmp : x;
  tmp := heap[o,a];
  heap[o,a] := heap[o,b];
  heap[o,b] := tmp;
}
