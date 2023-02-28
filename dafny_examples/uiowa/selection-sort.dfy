
// Selection sort on arrays

method SelectionSort(a: array<int>) 
  modifies a
  ensures isSorted(a)
  ensures multiset(old(a[..])) == multiset(a[..])
{
  var n := 0;
  while (n != a.Length)
    invariant 0 <= n <= a.Length
    invariant forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j] 
    invariant forall k1, k2 :: 0 <= k1 < k2 < n ==> a[k1] <= a[k2] 
    invariant multiset(old(a[..])) == multiset(a[..])
  {
    var mindex := n;
    var m := n + 1;
    while (m != a.Length)
      invariant n <= m <= a.Length
      invariant n <= mindex < m <= a.Length
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i] 
    {
      if (a[m] < a[mindex]) {
        mindex := m;
      }
      m := m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n] ;
    n := n + 1;
  }
}
