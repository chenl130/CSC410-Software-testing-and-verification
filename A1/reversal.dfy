// In place array reversal
predicate IsReverse(s : seq<int>, t : seq<int>)
{
    |s| == |t| && forall i: int :: 0 <= i < |s|  ==> s[i] == t[|t| - i - 1]
}


method Reverse(a: array<int>) 
   modifies a
   ensures IsReverse(a[..], old(a[..]))
{
   if a.Length <= 1 { return; } //no change if a is empty or contains only one element

   ghost var olda := a;
   
   var l, r := 0, a.Length - 1;
 
    while l < r
    invariant l+r == a.Length-1;
    invariant l < r+2;
    invariant l > 0 ==> IsReverse(a[..l], old(a[r+1..]))
    invariant l > 0 ==> IsReverse(a[r+1..], old(a[..l]))
    invariant  l > 0 ==> IsReverse(a[..l] + a[r+1 ..] , old(a[..l])+old(a[r+1..]))
    invariant l <= r ==> a[l .. r+1] == old(a[l .. r+1])
    {

        var temp1 := a[r];
        var temp2 := a[l];
        assert temp1 == olda[r];
        assert temp2 == olda[l];
        
        a[l], a[r] := a[r], a[l]; 

        assert a[l] == temp1;
        assert a[r] == temp2;
        
        r := r - 1;
        l := l + 1;
    }
    assert l == r || l == r+1;

    Rebuild(a[..],old(a[..]),l, r);
}

lemma Concat_element_reverse(s:seq<int>,t:seq<int>,p:int)
    requires IsReverse(s, t)
    ensures IsReverse(s+[p], [p]+t)
    {}

lemma Concat_seq_reverse(s1:seq<int>,t1:seq<int>,s2:seq<int>,t2:seq<int>)
    requires IsReverse(s1, t1)
    requires IsReverse(s2, t2)
    ensures IsReverse(s1+s2, t2+t1)
    {}

//odd number elements
lemma Rebuild1(s:seq<int>,t:seq<int>,l:int, r:int)
    requires |s| >= 1 && |s| == |t|
    requires l == r
    requires l + r == |s| - 1
    requires IsReverse(s[..l], t[r+1..])
    requires IsReverse(s[r+1..], t[..l])
    requires s[l] == t[l]
    ensures IsReverse(s,t)
{
    assert s[..] == s[..l] + [s[l]] + s[r+1..];
    assert t[..] == t[..l] + [t[l]] + t[r+1..];
    Concat_element_reverse(s[..l], t[r+1..], s[l]) ;
    Concat_seq_reverse(s[..l+1], t[r..], s[r+1..],t[..l]);
}

//even number element
lemma Rebuild2(s:seq<int>,t:seq<int>,l:int, r:int)
    requires |s| >= 1 && |s| == |t|
    requires l == r + 1
    requires l + r == |s| - 1
    requires IsReverse(s[..l], t[r+1..])
    requires IsReverse(s[r+1..], t[..l])
    ensures IsReverse(s,t)
{
    assert s[..] == s[..l] + s[r+1..];
    assert t[..] == t[..l] + t[r+1..];
}

lemma Rebuild(s:seq<int>,t:seq<int>,l:int, r:int)
    requires |s| >= 1 && |s| == |t|
    requires l == r || l == r+1
    requires l + r == |s| - 1
    requires l == r ==> s[l] == t[l]
    requires IsReverse(s[..l], t[r+1..])
    requires IsReverse(s[r+1..], t[..l])
    ensures IsReverse(s,t)
{
    if l == r
    {
        Rebuild1(s, t, l, r);
    }
    else
    {
        Rebuild2(s, t, l, r);
    }
}

