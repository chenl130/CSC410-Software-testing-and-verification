
method Find(a: array<nat>) returns (index: int)
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i != j) ==> a[i] != a[j]
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i < j) ==> a[i] < a[j]
    ensures 0 <= index ==> index < a.Length && a[index] == index
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != k
{
    if a.Length == 0 { return -1;}
    if a[0] == 0 { return 0;}

    assert a[0] > 0;
    AllGreater(a, 0, a.Length - 1);
    index := a.Length - 1;
    while index > 0 
    {
        if a[index] == index { return; }

        if a[0] == 0 { return 0;}

        index := index/2;
    }

    return -1;
}

lemma AllGreater(a: array<nat>, p:nat, q:nat)
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i != j) ==> a[i] != a[j]
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i < j) ==> a[i] < a[j]
    requires 0 <= p <= q <= a.Length - 1 
    requires a[p] > p
    ensures forall k :: p <= k <= q ==> a[k] > k
{  
   if p == q
   {}
   else 
   {
        AllGreater(a, p, q-1);
        assert a[q-1] > q-1;
   }
}
