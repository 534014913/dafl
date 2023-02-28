/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2021
   The University of Iowa
   
   Instructor: Cesare Tinelli

*/

/*
 This is a version of the counter that stores the conter 
 value in a separate Cell object, to demonstrate the use 
 of dynamic frames in Dafny.
*/
class Cell {
  var data: int;

  constructor (n: int)
    ensures data == n
  {
    data := n;
  }
}

class Counter
{
  // Abstract (public) fields
  ghost var Val: int;
  ghost var R: set<object>; // dynamic heap frame represented as a set of objects

  // Concrete (private) fields
  var incs: Cell;
  var decs: Cell;

  function Valid(): bool
    reads this, R
  {
    // Class invariant for concrete representation 
    incs != decs

    // Connection between abstract and concrete representation
    && R == {this, incs, decs}   // this heap frame is invariant
    && Val == incs.data - decs.data
  }

  constructor ()
    ensures Valid()
    ensures fresh(R - {this})
    ensures Val == 0
  {
    incs := new Cell(0);
    decs := new Cell(0);

    // ghost code
    Val := 0;
    R := { this, incs, decs };
  }

  method GetVal() returns (x: int)
    requires Valid()
    ensures Valid()
    ensures x == Val
  {
    x := incs.data - decs.data;
  }

  method Inc()
    modifies R
    requires Valid()
    ensures Valid()
    ensures R == old(R)
    ensures Val == old(Val) + 1
  {
    incs.data := incs.data + 1;

    // ghost code
    Val := Val + 1;
    R := { this, incs, decs };
  }

  method Dec()
    modifies R
    requires Valid()
    ensures Valid()
    ensures R == old(R)
    ensures Val == old(Val) - 1
  {
    decs.data := decs.data + 1;

    // ghost code
    Val := Val - 1;
    R := { this, incs, decs };
  }
}

method Main()
{
  var c := new Counter();  assert c.Val == 0;
  c.Inc();                 assert c.Val == 1;
  c.Inc();                 assert c.Val == 2;
  c.Dec();                 assert c.Val == 1;
  c.Inc();                 assert c.Val == 2;
}
