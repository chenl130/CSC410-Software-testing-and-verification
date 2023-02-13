/*
Given a sequence of positive natural numbers [a b c ...] with size n
return T(n) = a(a-1)/2 + b(b-1)/2 + ....
*/
function SumGaussFormula(s:seq<nat>): nat
    requires |s| > 0 ==> forall i :: 0 <= i < |s| ==> s[i] >= 1
{
    if |s| == 0 then 0 
    else s[0] * (s[0] - 1)/2 + SumGaussFormula(s[1..])
}

method Game(n: nat) returns (score: nat)
    requires n > 0 
    ensures score == n * (n - 1) / 2 
{
    var stacks := [n];
    score := 0;

    while |stacks| > 0
    invariant forall i :: 0 <= i < |stacks| ==> stacks[i] >= 1 //Needed for calling lemmas
    invariant score + SumGaussFormula(stacks) == n * (n - 1) / 2 //Needed to get postcondition 
    invariant SumGaussFormula(stacks) >= 0 //Needed to help prove decrease expression is bounded by zero
    decreases |stacks| + 2*SumGaussFormula(stacks) //if split, then sum decrease by j*k at least & |s| increase by 1; if remove sum no change & |s|-1
    //2* is needed to insure strictly decrease, since we can only prove SumGaussFormula(stacks) decrease by j*k>=1 and |stacks| increase by 1 each time when spliting boxes
    {
        var i :| 0 <= i < |stacks|;

        //define ghost variables needed to be used in either cases
        ghost var oldScore := score;  //score till last last iteragtion
        ghost var oldStacks := stacks; //stacks before next split/remove
        ghost var oldLseq := stacks[..i]; //stacks on the left side of the stack that will be splitted/removed
        ghost var oldRseq := stacks[i + 1..]; //stacks on the right side of the stack that will be splitted/removed
        ghost var oldi := stacks[i]; //number of boxes in the stack that will be splitted/removed
        ghost var oldSumGF := SumGaussFormula(stacks); //add this ghost variable to reduce running time


        if stacks[i] == 1 //case 1: remove this stack with only one box
        { //score no change, WTS SumGaussFormula(stacks) no change & |stack| decrease
            assert stacks[i]*(stacks[i]-1)/2 == 0; 
            stacks := stacks[..i] + stacks[i + 1..];

            //WTS the only diff between sum(oldstack) & sum(stack) is term si*(si-1)/2
            split_into_three_seq_2(oldStacks, i); // oldSumGF = sum(oldstack) == sum(left) + si*(si-1)/2 + sum(right)
            split_into_two_seq(stacks, oldLseq, oldRseq); // sum(stack) == sum(left) + sum(right)
            
            //WTS SumGF has no change (|stacks| no change) ==> invariant holds
            assert oldSumGF == SumGaussFormula(stacks); 
            //no need to prove decrease, since dafny itself has proved 2*SumGaussFormula(stacks) no change and |stacks| decrease by 1
        }
        else //case 2: split this stack into two stacks
        {//score increase by j*k, WTS 2*SumGaussFormula(stacks) decrease by 2*j*k>1 & |stacks| increase by 1
            var j, k :| stacks[i] == j + k && j > 0 && k > 0;
            score := score + j * k; //score increase by j*k
            stacks := [j, k] + stacks[..i] + stacks[i + 1..];

            //WTS sum(stack) = sum(left) + sum(right) + sum([j,k])
            assert stacks == [j, k] + oldLseq + oldRseq;
            split_into_three_seq(stacks, [j, k], oldLseq, oldRseq);

            //WTS sum(oldstack) = sum(left) + sum(right) + sum(olds[i])
            assert oldStacks == oldLseq + [oldi] + oldRseq;
            split_into_three_seq(oldStacks, oldLseq,[oldi], oldRseq);

            //the only diff between old and current stack is diff(sum([j,k], sum(olds[i])
            assert SumGaussFormula([oldi]) == oldi * (oldi-1)/2;
            assert SumGaussFormula([j,k]) == SumGaussFormula([j])+SumGaussFormula([k])==j*(j-1)/2 + k*(k-1)/2;
            SumGaussValueChangeWhenSplit2(oldi, j, k); //lemma that help calculate sum(olds[i]) - sum([j,k] to solve time-out issue
            assert SumGaussFormula(oldStacks) - SumGaussFormula(stacks) == SumGaussFormula([oldi]) - SumGaussFormula([j,k]) == j*k;
            
            //WTS |stacks| increase by 1 
            assert |stacks| == |oldStacks| + 1; 

            //WTS score + sum(stack no change) == n(n-1)/2
            calc ==
            {
                oldScore + SumGaussFormula(oldStacks);
                oldScore + j*k - j*k + SumGaussFormula(oldStacks);
                score + SumGaussFormula(oldStacks) - j*k;
                score + SumGaussFormula(stacks);
                n * (n - 1) / 2;
            }
            //decrease expression has been proved by dafny itself, i.e. 2*j*k >= 2 > 1
        }

        //SumGaussNonNegative(stacks); //needed to lower bound decress expression
    }
    return;
}

//should I keep?????  helper lemma to prove invariant SumGaussFormula(stacks) >= 0
lemma SumGaussNonNegative(s:seq<nat>)
    requires |s| > 0 ==> forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures SumGaussFormula(s)>=0
    {}

/*WTS:
x = a + b where x>=2 and a>=1 and b>=1
then x(x-1) = a(a-1) + b(b-1) + 2ab
Note: cannot prove x(x-1)/ = a(a-1)/2 + b(b-1)/2 + ab directly cuz of time out
*/
lemma SumGaussValueChangeWhenSplit(a:nat, j:nat, k:nat)
    requires j >= 1 && k >= 1 
    requires a == j + k
    ensures a*(a-1) - j*(j-1) - k*(k-1) == 2*j*k
    ensures 2*j*k >=2
    //ensures a*(a-1)/2 - j*(j-1)/2 - k*(k-1)/2 == j*k
{
    assert j*k > 0;
    calc== 
    {
        a*(a-1);
        (a*a-a);
        ((j+k)*(j+k)-(j+k));
        (j*j + j*k + j*k + k*k - j- k);
        (j*j - j + k*k - k + 2*j*k);
        ((j * j - j) + (k * k - k) + (2 * j * k));
        j*(j-1) + k*(k-1) + 2*j*k;
    }
}

/*
lemma to help prove EvenSumGauss
*/
lemma Even(n: nat)
    ensures n%2 == 0 ==> exists k:: n == 2*k
    ensures n%2 == 1 ==> exists k:: n == 2*k+1
{
    if n == 0 
    {
        assert 0 == 2 * 0;
    } 
    else 
    {
        Even(n - 1);
        if exists k :: n - 1 == 2 * k 
        {
            var k :| n == 2 * k + 1;
        } 
        else 
        {
            var k :| n - 1 == 2 * k + 1;
            calc == 
            {
                n;
                n - 1 + 1;
                2 * k + 1 + 1;
                2 * (k + 1);
            }
        }
    }
}

/*
helper lemma to solve /2 in original equation 
*/
lemma EvenSumGauss(i:nat)
    ensures exists k :nat :: i*(i-1) == 2*k
{
    Even(i);
    if i%2 == 0
    {
        var k :| i == 2 * k;
        assert i*(i-1) == 2*(k*2*k-k);
    }
    else
    {
        var k :| i-1 == 2 * k;
        assert i*(i-1) == 2*(2*k*k+k);
    }
}

/*WTS:
x = a + b where x>=2 and a>=1 and b>=1
then x(x-1)/2 = a(a-1)/2 + b(b-1)/2 + ab
*/
lemma SumGaussValueChangeWhenSplit2(a:nat, j:nat, k:nat)
    requires j >= 1 && k >= 1 
    requires a == j + k
    ensures a*(a-1)/2 - j*(j-1)/2 - k*(k-1)/2 == j*k
    //ensures a*(a-1)/2 - j*(j-1)/2 - k*(k-1)/2 == j*k
{
    SumGaussValueChangeWhenSplit(a,j,k);
    EvenSumGauss(a);
    EvenSumGauss(j);
    EvenSumGauss(k);
}

/* prepare for proving concat_three_seq
WTS:
if s == p+q, then SumGaussFormula(s) == SumGaussFormula(p) + SumGaussFormula(q)
*/
lemma split_into_two_seq(s:seq<nat>, p:seq<nat>, q:seq<nat>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    requires |p| > 0 ==> forall i :: 0 <= i < |p| ==> p[i] >= 1
    requires |q| > 0 ==> forall i :: 0 <= i < |q| ==> q[i] >= 1
    requires s == p+q
    ensures SumGaussFormula(s) == SumGaussFormula(p) + SumGaussFormula(q)
{
    if |p| == 0 //s == q and thus SumGaussFormula(s) ==  SumGaussFormula(q)
    {
        assert s == q;
    }
    else 
    {
        split_into_two_seq(s[1..], p[1..], q);//s == p+q ==> s[0] == p[0] ==> s[0]*(s[0]-1) == p[0]*(p[0]-1)
    }
}

/*
prepare for proving SumGaussFormula(stacks) 
== SumGaussFormula(stacks[..i]) + SumGaussFormula([stacks[i]]) + SumGaussFormula(stacks[i+1..])
WTS:
if s == p+q+r, then SumGaussFormula(s) == SumGaussFormula(p) + SumGaussFormula(q)
*/
lemma split_into_three_seq(s:seq<nat>, p:seq<nat>, q:seq<nat>, r:seq<nat>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    requires |p| > 0 ==> forall i :: 0 <= i < |p| ==> p[i] >= 1
    requires |q| > 0 ==> forall i :: 0 <= i < |q| ==> q[i] >= 1
    requires |r| > 0 ==> forall i :: 0 <= i < |r| ==> r[i] >= 1
    requires s == p+q+r
    ensures SumGaussFormula(s) == SumGaussFormula(p) + SumGaussFormula(q)+ SumGaussFormula(r)
{
    split_into_two_seq(p+q, p, q);
    split_into_two_seq(s, p+q, r);
}

/*
WTS:
if an element equals to 1, it doesn't impact SumGaussFormula
*/
lemma OneIgnore(s:seq<nat>, t:seq<nat>, l:seq<nat>, r:seq<nat>)
    requires s == l +[1]+r;
    requires t == l + r;
    requires |s| > 0 ==> forall i :: 0 <= i < |s| ==> s[i] >= 1;
    requires |t| > 0 ==> forall i :: 0 <= i < |t| ==> t[i] >= 1;
    requires |l| > 0 ==> forall i :: 0 <= i < |l| ==> l[i] >= 1;
    requires |r| > 0 ==> forall i :: 0 <= i < |r| ==> r[i] >= 1
    ensures SumGaussFormula(s) == SumGaussFormula(t);
{
    split_into_three_seq(s, l, [1], r);
    split_into_two_seq(t,l,r);
    assert SumGaussFormula([1]) == 0;
}

/*
WTS:
sgf(s) == sgf(s[..i]) + sgf(s[i+1..]) + s[i]*s[i-1]/2
*/
lemma split_into_three_seq_2(s:seq<nat>, index:nat)
    requires 0 <= index < |s|
    requires |s| > 0 ==> forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures |s| > 0 ==> SumGaussFormula(s[..index]) + s[index] * (s[index]-1)/2 + SumGaussFormula(s[index+1..]) == SumGaussFormula(s)
{
    if |s| == 1
    {}
    else if |s| == 2
    {}
    else
    {
        var p := s[..index];
        var q :=[s[index]];
        var r := s[index+1..];
        assert s == p + q + r;
        assert SumGaussFormula(q) == s[index] * (s[index]-1)/2;
        split_into_three_seq(s, p, q, r);
    }
}
