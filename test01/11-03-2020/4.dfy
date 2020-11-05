function C(n: nat): nat
{
    if n == 0 then 1 else (4 * n - 2) * C(n - 1) / (n + 1)
}

method calcC(n: nat) returns (res: nat)
  ensures res == C(n)
{
    assert 0 <= 0 <= n && 1 == C(0); //(ii)

    var i := 0;
    assert 0 <= i <= n && 1 == C(i); //(ii)
    res := 1;

    assert 0 <= i <= n && res == C(i); //I
    while i < n
        decreases n - i
        invariant 0 <= i <= n && res == C(i)
    {
        ghost var V0 := n - i;

        assert 0 <= i <= n && i < n && n - i == V0; //I && C && V=V0
        assert 0 <= i + 1 <= n && 0 <= n - (i+1) < V0; //(ii)

        assert (0 <= i <= n && i < n && n - i == V0) ==>(0 <= i + 1 <= n && 0 <= n - (i+1) < V0); //(iii)
        i := i + 1;
        res := (4 * i - 2) * res / (i + 1);

        assert 0 <= i <= n && 0 <= n - i < V0; //I && 0 <= V < V0
    }

    assert 0 <= i <= n  && i >= n; //I && ~C
    assert res == C(n);

    assert (0 <= i <= n  && i >= n) ==> (res == C(n)); //(iii)
}