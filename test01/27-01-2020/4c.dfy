function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}


method calcF(n: nat) returns (res: nat)  
 ensures res == F(n) 
{
    assert 0 <= 0 <= n && 0 == F(0) && 1 == F(0+1) && 2 == F(0+2); //(ii)

    var a, b, c := 0, 1, 2;

    assert 0 <= 0 <= n && a == F(0) && b == F(0+1) && c == F(0+2); //(ii)
    var i := 0;

    //I
    assert 0 <= i <= n && a == F(i) && b == F(i+1) && c == F(i+2); //(i)

    while i < n 
    decreases n - i //4.a
    invariant 0 <= i <= n //4.b
    invariant a == F(i) && b == F(i+1) && c == F(i+2)
    {
    ghost var V0 := n - i;

        //I ∧ C ∧ V=V0
    assert 0 <= i <= n && a == F(i) && b == F(i+1) && c == F(i+2) && i < n && n - i == V0; //(i)

    assert  0 <= i + 1 <= n && b == F(i + 1) && c == F(i + 1+1) && a+ c == F(i + 1 + 2) && 0 <= n - (i + 1)< V0;  //(ii)

    assert (0 <= i <= n && a == F(i) && b == F(i+1) && c == F(i+2) && i < n && n - i == V0) ==> (0 <= i + 1 <= n && b == F(i + 1) && c == F(i + 1+1) && a+ c == F(i + 1 + 2) && 0 <= n - (i + 1)< V0);//(iii)
    a, b, c := b, c, a + c;   

    assert  0 <= i + 1<= n && a == F(i + 1) && b == F(i + 1+1) && c == F(i + 1 + 2) && 0 <= n - (i + 1)< V0;   //(ii)   
    i := i + 1;

        //I ∧ 0 <= V < V0
    assert  0 <= i <= n && a == F(i) && b == F(i+1) && c == F(i+2) && 0 <= n - i < V0; //(i)
    }
    //I ∧ ¬C
    assert 0 <= i <= n && a == F(i) && b == F(i+1) && c == F(i+2) && i >= n; //(i)
    assert a == F(n);//(ii)

    assert (0 <= i <= n && a == F(i) && b == F(i+1) && c == F(i+2) && i >= n) ==> (a== F(n)); //(iii)
    res := a;
    //assert pos condition
    assert res == F(n); //(i)
}
