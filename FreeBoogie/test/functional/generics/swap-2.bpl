type Ref;
type Field x;
var heap : <x>[Ref, Field x]x;

const fi : Field int;
const fr : Field int;

procedure swap<x>(o : Ref, a : Field x, b : Field x) {
  var tmp : x;
  tmp := heap[o,a];
  heap[o,a] := heap[o,b];
  heap[o,b] := tmp;
}

procedure main() {
  var o : Ref;
  entry:
    call swap(o,fi,fr); /* swap<`int> should be inferred */
// EXPSPEC
//    call swap<`int>(o, fi, fi);
//    call swap<`ref>(o, fr, fr); /* should give an error */
}

