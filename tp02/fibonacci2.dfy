function fib(n : nat ) : nat
  decreases n
{
    if n < 2 then n else fib(n - 2) + fib(n - 1)
}

method computeFib (n : nat) returns (x : nat)
    ensures x == fib(n)
{
    assert true; //precondition 
    assert 0 <= 0 <= n && 0 == fib(0) && 1 == fib(0+1);
    var i := 0;
    assert 0 <= i <= n && 0 == fib(i) && 1 == fib(i+1);
    x := 0;
    assert 0 <= i <= n && x == fib(i) && 1 == fib(i+1);
    var y := 1;

    assert 0 <= i <= n && x == fib(i) && y == fib(i+1); //I

    while i < n
        decreases n - i
        invariant 0 <= i <= n
        invariant x == fib(i) && y == fib(i+1)
    {
        ghost var V0 := n - i;
        assert 0 <= i <= n && x == fib(i) && y == fib(i+1) && i < n && n - i == V0; //I && C && V=V0
        assert 0 <= i + 1<= n && y == fib(i + 1) && x+y == fib(i+2) && 0 <= n - (i+1) < V0;

        assert (0 <= i <= n && x == fib(i) && y == fib(i+1) && i < n && n - i == V0) ==>(0 <= i + 1<= n && y == fib(i + 1) && x+y == fib(i+2) && 0 <= n - (i+1) < V0);

        x, y := y, x + y; 

        assert 0 <= i + 1<= n && x == fib(i + 1) && y == fib(i+2) && 0 <= n - (i+1) < V0;

        i := i + 1;

        assert 0 <= i <= n && x == fib(i) && y == fib(i+1) && 0 <= n - i < V0;// I && 0 <= V < V0
    }

    assert 0 <= i <= n && x == fib(i) && y == fib(i+1) && i >= n; //I && ~C
    assert x == fib(n); //POST CONDITION

    assert ( 0 <= i <= n && x == fib(i) && y == fib(i+1) && i >= n) ==> ( x == fib(n));
}

method testComputeFib() {
    var f := computeFib(3);
    assert f == 2;
}