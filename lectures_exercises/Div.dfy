// nat = numero natural maior ou igual a zero
method div(n: nat, d: nat) returns(q: nat, r :nat)
    //pre-condition
    requires d > 0
    //post-condition
    ensures q + d * r == n && r < d
{
    q := 0;
    r := n;

    // invariant: verdade antes e no fim do ciclo, e permanecer assim no inicio e fim de cada iteração,
    // no entanto pode ser violado a meio
    while r >= d invariant q * d + r == n{
        q := q + 1;
        r := r - d;
    }
}

method main(){

    var q, r := div(15,6);

    //testar
    assert q == 2;
    assert r == 3;

    print "q= ", q, " r= ", r , "\n";

}