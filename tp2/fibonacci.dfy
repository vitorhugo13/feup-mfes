function fib(n : nat ) : nat
  decreases n
{
    if n < 2 then n else fib(n - 2) + fib(n - 1)
}


//os asserts, ghost, wp sao para o exercicio 1c)
method computeFib (n : nat) returns (x : nat)
    requires n > 0 //redundant
    ensures x == fib(n)
{

    assert true; //precondition ( alinea c)
    //wp?
    assert 0 <= 0 <= n && 0 == fib(0) && 1 == fib(0+1); //weakest pre condition

    var i := 0;
    x := 0;
    var y := 1;

    assert 0 <= i <= n && x == fib(i) && y == fib(i+1); //(invariant verdade antes do ciclo)
    while  i < n 
        //invariant
        invariant 0 <= i <= n && x == fib(i) && y == fib(i+1) 
        //variant
        decreases n - i

    {
        ghost var V0 := n - i; //V = V0
        assert i < n && 0 <= i <= n && x == fib(i) && y == fib(i+1); //C && I - invariant verdadeiro antes de executar cada it.
        //wp?
        assert 0 <= i + 1 <= n && y == fib(i + 1) && x + y == fib(i+2) && 0  <= n - i  - 1 < V0; //wp

        x, y := y, x + y; // multiple assignment
        i := i + 1;
        assert 0 <= i <= n && x == fib(i) && y == fib(i+1) && 0  <= n - i < V0; //C && I - invariant verdadeiro apos executar cada it.

    }

    assert i >= n && 0 <= i <= n && x == fib(i) && y == fib(i+1); //!C && I
    assert x == fib(n); //post condition (alinea c)
}

//testing pos condition
method testComputeFib() {
    var f := computeFib(3);
    assert f == 2;
}