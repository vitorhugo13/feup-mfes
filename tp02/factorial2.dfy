function method fact(n: nat) : nat
  decreases n
{
    if n == 0 then 1 else n * fact(n-1)
}
method factIter(n: nat) returns (f : nat)
    ensures f == fact(n)
{
    assert true;//pre condition
    assert 0 <= 0 <= n && 1 == fact(0);
    assert (true) ==> (0 <= 0 <= n && 1 == fact(0));
    f := 1;
    assert 0 <= 0 <= n && f == fact(0);
    var i := 0;
    assert 0 <= i <= n && f == fact(i);//I
    while i < n
        decreases n - i
        invariant 0 <= i <= n && f == fact(i)
    {
        ghost var V0 := n - i;
        assert 0 <= i <= n && f == fact(i) && i < n && n - i == V0;//I && C && V=V0
        assert 0 <= i+1 <= n && f * (i+1) == fact(i+1) &&  0 <= n - (i+1) < V0;
        assert (0 <= i <= n && f == fact(i) && i < n && n - i == V0) ==> (0 <= i+1 <= n && f * (i+1) == fact(i+1) &&  0 <= n - (i+1) < V0);
        i := i + 1;
        assert 0 <= i <= n && f * i == fact(i) &&  0 <= n - i < V0;
        f := f * i;
        assert 0 <= i <= n && f == fact(i) &&  0 <= n - i < V0;// I && 0 <= V < V0

    }
    assert 0 <= i <= n && f == fact(i) &&  i >= n;  //I && ~C
    assert f == fact(n); //pos condition
    assert (0 <= i <= n && f == fact(i) &&  i >= n) ==> (f == fact(n));
}
