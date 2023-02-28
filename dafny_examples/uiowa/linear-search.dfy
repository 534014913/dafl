
// Linear search

method LinearSearch<T>(a: array<T>, P: T -> bool)
returns (n: int)  
  ensures 0 <= n <= a.Length 
  ensures n == a.Length || P(a[n])
{ 
  n := 0; 
  while n != a.Length 
    invariant 0 <= n <= a.Length 
  {
    if P(a[n]) { return; } else { 
      n := n + 1;   
    }
  }
}


method LinearSearchTrivialized<T>(a: array<T>, P: T -> bool)
returns (n: int)  
  ensures 0 <= n <= a.Length 
  ensures n == a.Length || P(a[n])

{ 
  n := a.Length;
}


method LinearSearch2<T>(a: array<T>, P: T -> bool)
returns (n: int)  
  ensures 0 <= n <= a.Length 
  ensures n == a.Length || P(a[n])
  ensures n == a.Length ==> 
            forall i :: 0 <= i < a.Length ==> !P(a[i])
{ 
  n := 0; 
  while n != a.Length 
    invariant 0 <= n <= a.Length 
    invariant forall i :: 0 <= i < n ==> !P(a[i])
  {
    if P(a[n]) { return; } else { 
      n := n + 1;   
    }
  }
}

method LinearSearch3<T>(a: array<T>, P: T -> bool)
returns (n: int)  
  ensures 0 <= n <= a.Length 
  ensures n == a.Length || P(a[n])
  ensures forall i :: 0 <= i < n ==> !P(a[i])
{ 
  n := 0; 
  while n != a.Length 
    invariant 0 <= n <= a.Length 
    invariant forall i :: 0 <= i < n ==> !P(a[i])
  {
    if P(a[n]) { return; } else { 
      n := n + 1;   
    }
  }
}
