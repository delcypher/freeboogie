// heapsucc0.bpl

type ref;
type name;

var Heap : [ref, name]int;
const unique FIELD : name;
const unique OTHERFIELD : name;
var x : int, y : int, z : int;

procedure M(this : ref)
  modifies y, z, Heap;
{
  start:
    y := Heap[this, FIELD];
    Heap[this, OTHERFIELD] := x;
    z := Heap[this, FIELD];
    goto StartCheck;

  StartCheck:
    assert y == z && x == Heap[this,OTHERFIELD] && y == Heap[this,FIELD];
    return;
}
