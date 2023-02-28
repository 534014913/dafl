/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2021
   The University of Iowa
   
   Instructor: Cesare Tinelli
*/

// Parametric FIFO queue
// Implementation uses an array to store the queue elements
// in order of arrival

class Queue<T> {
  // Abtract representation of the queue's elements
  ghost var Content: seq<T>;

  // Concrete implementation of the queue
  // container for the queue's elements
  var a: array<T>;
  // size of the queue
  var n: nat;

  predicate Valid()
  reads this, a;
  {
    // Concrete class invariant
    n <= a.Length && 
    0 < a.Length &&

    // Connection between abstract and concrete state
    Content == a[0..n]
  }

  constructor (d: T)
    ensures Valid()
    ensures fresh(a)
    ensures Content == []
  {
    a := new T[5](_ => d); // initializes every array element to d
    n := 0;

    // ghost code
    Content := [];
  }

  method front() returns (e: T)
    requires Valid()
    requires Content != []
    ensures Valid()
    ensures Content == old(Content)
    ensures e == Content[0]
  {
    e := a[0]; 
  }
 
  method enqueue(e: T)
    modifies this, a
    requires Valid()
    ensures Valid()
    ensures old(n) < old(a.Length) ==> a == old(a)
    ensures old(n) == old(a.Length) ==> fresh(a)
    ensures Content == old(Content) + [e]
  {
    if (n == a.Length) {
      var b := new T[2 * a.Length](_ => e);
      forall i:int | 0 <= i < n {
        b[i] := a[i];
      }
      a := b;
    }
    a[n] := e;
    n := n + 1;

    // ghost code
    Content := a[0..n];
  }

  method dequeue() returns (e: T)
    modifies this, a;
    requires Content != [];
    requires Valid();
    ensures Valid();
    ensures a == old(a);
    ensures Content == old(Content[1..])
    ensures [e] + Content == old(Content)
  {
    e := a[0];
    n := n - 1;
    forall i:int | 0 <= i < n {
      a[i] := a[i + 1];
    }

    // ghost code
    Content := a[0..n];
  }
}

method test ()
{
  var q := new Queue<int>(0);  assert q.Content == [];
  q.enqueue(1);                assert q.Content == [1];
  q.enqueue(2);                assert q.Content == [1,2];
  q.enqueue(3);                assert q.Content == [1,2,3];
  q.enqueue(2);                assert q.Content == [1,2,3,2];
  q.enqueue(4);                assert q.Content == [1,2,3,2,4];

  var f := q.front();          assert f == 1 && q.Content == [1,2,3,2,4];
  f := q.dequeue();            assert           q.Content == [2,3,2,4];
  q.enqueue(5);                assert           q.Content == [2,3,2,4,5];
}
