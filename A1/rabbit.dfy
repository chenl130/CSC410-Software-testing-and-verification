function method unpair(n: nat): (nat, nat)
{
    // Add an implementation for this
    if n == 0 then (0, 0) else 
      var (x, y) := unpair(n - 1);
      if x > 0 then (x - 1, y + 1) else (y + 1, 0)
}


function method pick(i: nat): nat
{
  var (x, y) := unpair(i);
  x + i * y
}

lemma kExists(a: nat, b: nat) 
  ensures exists k : nat :: (a, b) == unpair(k)
{
  if a + b == 0 { 
    assert unpair(0) == (a, b);
  }
  else {
    kExists(0, a + b - 1);
    ghost var k : nat :| (0, a + b - 1) == unpair(k);
    assert unpair(k + 1) == (a + b, 0);
    allPairsWithSameSum(a, b, k, b);
    assert unpair(k + b + 1) == (a + b - b, 0 + b);
  }
}

lemma allPairsWithSameSum(x: nat, y: nat, k: nat, a: nat)
  requires x + y > 0
  requires unpair(k + 1) == (x + y, 0)
  requires x + y - a >= 0
  ensures (x + y - a, 0 + a) == unpair(k + 1 + a)
{
  if a == 0 {
    assert unpair(k + 1) == (x + y, 0);
  } else {
    allPairsWithSameSum(x, y, k, a - 1);
    assert (x + y - a, 0 + a) == unpair(k + 1 + a);
  }
}

method catchTheRabbit(a: nat, b: nat)
{
var t := 0;
  // prove that this loop terminates and therefore the rabbit is caught
  kExists(a, b); 
  ghost var k : nat :| (a, b) == unpair(k);
  while a + t * b != pick(t) 
    invariant t <= k
    decreases k - t
    { t := t + 1; }
}
