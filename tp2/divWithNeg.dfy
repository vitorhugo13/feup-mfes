/*

Generalize the example of integer division (Div.dfy) to also work with 
negative numbers (i.e., with variables of type int). 
Notice that the remainder should always be non-negative.
Hints: Create an auxiliary function method abs to obtain the absolute value 
of an integer. In the specification of the new version of div, 
you need to revise the postcondition for r. In the implementation of 
the new version of div, you may distinguish two cases: if n is positive, 
r starts with value n and needs to be decreased until reaching the desired 
interval; if n is negative, r starts with value n and needs to be increased 
until reaching the desired interval. In the loop invariant(s) you may need to 
add the range of values of r. 

*/
function method abs(x:int) : nat
{
  if x < 0 then -x else x
}

//só aceita naturais (exercicio da aula teorica)
method div(n: nat, d: nat) returns (q: nat, r: nat)
 requires d > 0
 ensures 0 <= r < d && q * d + r == n
{
  q := 0;
  r := n;  
  while r >= d
    decreases r
    invariant q * d + r == n 
  {
    q := q + 1;
    r := r - d;
  }
}
method divInt(n: int, d: int) returns (q: int, r: nat)
    requires d != 0
    ensures 0 <= r < abs(d) && q * d + r == n
{
    q, r := div(abs(n), abs(d));
    assert 0 <= r < abs(d) && q * abs(d) + r == abs(n);

    if n >= 0 { 

        assert 0 <= r < abs(d) && q * abs(d) + r == n;

        if d < 0 {
            assert 0 <= r < abs(d) && (-q) * d + r == abs(n);
            q := -q;
            assert 0 <= r < abs(d) && q * d + r == n;

        }
    }
    else{
        assert 0 <= r < abs(d) && q * abs(d) + r == -n;
        assert 0 <= r < abs(d) && -q * abs(d) - r == n;

        if d > 0 {
            assert 0 <= r < abs(d) && (-q) * d - r == n;
            if r == 0 {
                q := -q;
                assert 0 <= r < abs(d) && q * d + r == n;
                
            }
            else { 
                assert 0 <= r < abs(d) && (-q-1) * d + (d - r) == n;
                q,r := -q-1, d-r;
                assert 0 <= r < abs(d) && q * d + r == n;
            }
        }
        else {
            assert 0 <= r < abs(d) && q * d - r == n;
            if r == 0 {
                assert 0 <= r < abs(d) && q * d + r == n;

            }
            else {
                assert 0 <= r < abs(d) && (q + 1) * d + (-d - r) == n;
                q, r := q+1, -d-r;
                assert 0 <= r < abs(d) && q * d + r == n;

            }
        }
    }
}

// A simple test case (checked statically!)
method Main()
{
    var q, r := divInt(15, 6);
    assert q == 2;
    assert r == 3;
    print "q = ", q, " r=", "\n";
}
