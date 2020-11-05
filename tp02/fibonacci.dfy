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
    var i := 0;
    x := 0;
    var y := 1;

    while  i < n 
        //invariant
        invariant 0 <= i <= n && x == fib(i) && y == fib(i+1) 
        //variant
        decreases n - i
    {
        x, y := y, x + y; // multiple assignment
        i := i + 1;
    }

}

//testing pos condition
method testComputeFib() {
    var f := computeFib(3);
    assert f == 2;
}