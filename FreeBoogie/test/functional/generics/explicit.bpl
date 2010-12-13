function update1d<x,z>([x]z,x,z) returns ([x]z);
function update2d<x,y,z>([x,y]z,x,y,z) returns ([x,y]z);
function select1d<x,z>([x]z,x) returns (z);
function select2d<x,y,z>([x,y]z,x,y) returns (z);

axiom (forall<x,z> a:[x]z, i:x, v:z :: select1d(update1d(a,i,v),i)==v);
// EXPSPEC
//axiom (forall<x,y,z> a:[x,y]z, i1:x, i2:y, v:z::
//  select2d<`x,`y,`z>(update2d<`x>(a,i1,i2,v),i1,i2)==v);

