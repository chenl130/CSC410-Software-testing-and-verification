function gcd(a: nat, b: nat): nat
   requires a > 0 && b > 0
{   
   if a == b then a else
   if b > a then gcd(a,b - a) else
    gcd(a - b,b) 
}

predicate divides(a: nat, b:nat)
   requires a > 0 
{
  exists k: nat :: b == k * a
}

lemma dividesSubtraction(a: nat, b: nat, k: nat)
    requires a > 0 && b > 0 && k > 0 && b > a
    requires divides(k, a) && divides(k, b)
    ensures divides(k, b - a)
{
    var m :| a == m * k;
    var n :| b == n * k;

    calc {
        b - a;
        ==
        n*k - m*k;
        ==
        (n - m) * k; // k needs to be written afterwards only!
    }
}

lemma dividesGCD(a: nat, b:nat, k: nat) 
    requires a > 0 &&  b > 0 && k > 0 
    requires divides(k, a) && divides(k, b)
    ensures divides(k, gcd(a,b))
{
if a == b 
{} 
else if b > a 
{
    dividesSubtraction(a, b, k);
    calc {
        gcd(a, b);
        ==
        gcd(a, b - a);
    }
} else 
{
    dividesSubtraction(b, a, k);
    calc {
        gcd(a, b);
        ==
        gcd(a - b, b);
    }
}
}
