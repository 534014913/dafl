function count(s: seq<bool>): nat
  decreases s
{
   if s == [] then 0 else
   (if s[0] then 1 else 0) + count(s[1..])
}

lemma {:induction s} DistributiveLemma(s: seq<bool>, t: seq<bool>)
   decreases s
   ensures count(s + t) == count(s) + count(t)
{
  if s == [] {
  }
  else {
    DistributiveLemma(s[1..], t);
    assert s + t == s[0..1] + (s[1..] + t);
  }
}

lemma {:induction s} Lemma1(s: seq<bool>, t: seq<bool>)
   decreases s
   ensures count(s + t) >= count(t)
{
  if s == [] {
  }
  else {
    Lemma1(s[1..], t);
    assert s + t == s[0..1] + (s[1..] + t);
  }
}


function sum(s: seq<int>): int
  decreases s
{
   if s == [] then 0 else
   s[0] + sum(s[1..])
}

lemma {:induction s} DistributiveLemma2(s: seq<int>, t: seq<int>)
   decreases s
   ensures sum(s + t) == sum(s) + sum(t)
{
  if s == [] {
  }
  else {
    DistributiveLemma2(s[1..], t);
    assert s + t == s[0..1] + (s[1..] + t);
  }
}

lemma {:induction s} PosLemma(s: seq<int>)
   decreases s
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0;
    requires s != [];
    ensures sum(s) >= s[0] ;
{
/*  if s == [] {
  }
  else {
    //PosLemma(s[1..]);
    ////assert a + b == a[0..1] + (a[1..] + b);
  }
*/
}

function greatest(m: int, n: int): int
{
 if m > n then m else n
}

function max(s: seq<int>): int
  decreases s
  requires s != []
{
   if |s| == 1 then s[0] 
   else greatest(s[0], max(s[1..]))
}

lemma {:induction s} MaxLemma(s: seq<int>, t: seq<int>)
  decreases s
  requires s != []
  requires t != []
  ensures max(s + t) == greatest(max(s), max(t))
{
  if |s| == 1 {
  }
  else {
    MaxLemma(s[1..], t);
    assert s + t == s[0..1] + (s[1..] + t);
  }
}


/*
*/