// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
  decreases n
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(x: real, n: nat) returns (p : real)
  // requires !(x == 0.0 && n == 0) não é certo que é preciso
  ensures p == power(x, n)
{
    // start with p = x^0
    p := 1.0;
    var i := 0;
    // iterate until reaching p = x^n
    while i < n
      decreases n - i
      invariant 0 <= i <= n && p == power(x, i)
    {
        p := p * x;
        i := i + 1;
    }
}

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n);
  decreases n;
{
    if n == 0 {
        return 1.0;
    }
    else if n == 1 {
        return x;
    }
    else if n % 2 == 0 {
        distributiveProperty(x,  n/2, n/2); // recall lemma here
        var temp := powerOpt(x, n/2);
        return temp * temp;
    }
    else {
        distributiveProperty(x, (n-1)/2, (n-1)/2); // recall lemma here  
        var temp := powerOpt(x, (n-1)/2);
        return temp * temp * x;
    } 
}

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'. (in this case the code in body is not needed)

//for {:induction false } we need to add the code in the body
lemma {:induction false} distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{
  // The body below is not needed, because Dafny deduces the proof cases and steps automatically.
  // To use the proof below, deactivate automatic induction, with {:induction false}.
  
    if a == 0 {
        // base case
        calc == {
            power(x, a) * power(x, b);
            power(x, 0) * power(x, b); // substitution
            1.0 * power(x, b); // by the definition of power
            power(x, b); // neutral element of "*"
            power(x, a + b); // neutral element of "+"
        }
    }
    else {
        // recursive case, assuming property holds for a-1 (proof by induction)
        distributiveProperty(x, a-1, b); 
        // now do the proof
        calc == {
            power(x, a) * power(x, b);
            (x * power(x, a-1)) * power(x, b); // by the definition of power
            x * (power(x, a-1) * power(x, b)); // associative property
            x * power(x, a + b - 1); // this same property for a-1
            power(x, 1 + (a - 1 + b));
            power(x, a + b); // definition of power
        }
    }
  
}

// A simple test case to make sure the specification is adequate.
method testPower() {
    var p1 := powerIter(2.0, 5);
    var p2 := powerOpt(2.0, 5);
    assert p1 == 32.0;
    assert p2 == 32.0;
}