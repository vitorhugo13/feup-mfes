function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

method calcR(n: nat) returns (r: nat)
    ensures r == R(n) 
{
    r := 0;
    var i := 0;
    while i < n 
        decreases n - i //4.a
        invariant 0 <= i <= n && r == R(i) //4.b
    {
       i := i + 1;

       if r  > i {
           r := r - i;
       } 
       else {
            r := r + i;
        }
    }
}

method main(){
    var r := calcR(8);
    assert r == 16;
}