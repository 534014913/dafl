/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2021
   The University of Iowa
   
   Instructor: Cesare Tinelli
*/


// Parametric FIFO queue
// using two internal sequences to store queue elements

// The use of two sequences, one to enqueue to and one dequeue from,
// allow the implementation of a enqueue and a dequeue operation 
// whose runtine, in _both_ cases, is linear in the size of the queue.

class Queue<T> {
 
  // Elements of the queue in order from less to most recent
  ghost var Content: seq<T>;

  var incoming: seq<T>;  // enqueued values are inserted at the front here
  var outgoing: seq<T>;  // values are dequeued from the front here

  // Specification function:
  // returns reverse of input sequence
  function reverse(s: seq<T>): seq<T>
    decreases s
    ensures |s| == |reverse(s)|
    ensures forall i:nat :: i < |s| ==> s[i] == reverse(s)[|s|-1-i]
  {
    if s == [] then
      []
    else
      reverse(s[1..]) + s[0..1]
  }

  // Class invariant predicate
  predicate Valid()
    reads this
  {
    Content == outgoing + reverse(incoming)
  }

  // Empty queue constructor
  // Starts with an empty queue
  constructor ()
    ensures Valid()
    ensures Content == []
  {
     incoming := [];
   	 outgoing := [];

	   Content := [];
  }

  // Enqueuing operation
  method enqueue(e: T)
    modifies this
    requires Valid()
    ensures Content == old(Content) + [e]
    ensures Valid()
  {
    incoming := [e] + incoming; // constant time operation 
                                // (because the cost of (s1 + s2) is linear
                                //  in the size of s1)
    Content := Content + [e];
  }

  // Axiliary (private) method: 
  // it progressively moves any elements from the front of incoming
  // to the front of outgoing 
  // Note that its contract is expressed in terms of the concrete state 
  // That is OK since this is a private method
  method moveFromIncoming()
    modifies this
    requires Valid()
    requires outgoing == []
    ensures incoming == []
    ensures outgoing == reverse(old(incoming))
    ensures Valid()
  {
    while incoming != []
      decreases |incoming|;
      invariant reverse(incoming) + outgoing == reverse(old(incoming));
    {
      outgoing := incoming[0..1] + outgoing; // all constant time operations
      incoming := incoming[1..];             // all constant time operations
    }
 
    Content := outgoing;
  }
 
  // Front operation: it returns the oldest element of the queue
  // It does not modify the queue
  method front() returns (e: T)
    modifies this
    requires Valid()
    requires Content != []
    ensures Valid()
    ensures Content == old(Content)
    ensures e == Content[0]
  {
    if outgoing == [] { 
      moveFromIncoming(); 
    }
    e := outgoing[0]; // constant time operation 
  }

  // Dequeuing operation: it removes and returns the oldest element of the queue
  method dequeue() returns (e:T)
    modifies this
    requires Valid()
    requires Content != []
    ensures Content == old(Content[1..])
    ensures [e] + Content == old(Content)
    ensures Valid()
  {
    if outgoing == [] { 
      moveFromIncoming(); 
    }
    e := outgoing[0];           // constant time operation 
    outgoing := outgoing[1..];  // constant time operation 

    Content := Content[1..];
  }
}


method test2 ()
{
  var q := new Queue<int>();  assert q.Content == [];
  q.enqueue(1);                assert q.Content == [1];
  q.enqueue(2);                assert q.Content == [1,2];
  q.enqueue(3);                assert q.Content == [1,2,3];
  q.enqueue(2);                assert q.Content == [1,2,3,2];
  q.enqueue(4);                assert q.Content == [1,2,3,2,4];

  var f := q.front();          assert f == 1 && q.Content == [1,2,3,2,4];
  f := q.dequeue();            assert           q.Content == [2,3,2,4];
  q.enqueue(5);                assert           q.Content == [2,3,2,4,5];
}
