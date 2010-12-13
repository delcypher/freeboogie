type Ref;
var heap : [Ref]int;
function P(x : int) returns (bool);
function Q(x : int, y : int) returns (bool);
procedure Callee(x : int) returns (y : int);
  requires P(x);
  modifies heap;
  ensures Q(x, y);

procedure Caller(v : int) returns (w : int) {
  assume P(v);
  call w := Callee(v);
  assert Q(v, w);
}

