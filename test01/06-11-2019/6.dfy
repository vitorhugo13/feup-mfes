type T = int // example 

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
method merge(a: array<T>, b: array<T>) returns (c: array<T>) {
    c := new T[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b'

    // Repeatedly pick the smallest element from 'a' and 'b' and copy it into 'c':
    while i < a.Length || j < b.Length {
        if i < a.Length && (j == b.Length  || a[i] <= b[j]) {
            c[i + j] := a[i];
            i := i+1;
        } 
        else {
            c[i + j] := b[j];
            j:= j+1;
        }
    }
}

// Checks if the first 'n' elements in array 'a' are sorted.
predicate sorted(a: array<T>, n : nat)
  requires n <= a.Length
  reads a
{ forall i, j :: 0 <= i < j < n ==> a[i] <= a[j] }

// Obtain the multiset corresponding to the first 'n' elements in array 'a'.
function elems(a: array<T>, n: nat): multiset<T>
  requires n <= a.Length
  reads a
{ multiset(a[..n]) }
 
method testMerge() {
    var a: array<T> := new T[3] [1, 3, 5];
    var b: array<T> := new T[2] [2, 4]; 
    var c := merge(a, b);
    assert a[..a.Length]  == [1, 3, 5];
    assert b[..b.Length]  == [2, 4];
    assert elems(c, c.Length) == multiset{1, 2, 3, 4, 5};
    assert c[..] == [1, 2, 3, 4, 5];
}