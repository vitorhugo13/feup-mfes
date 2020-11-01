
type T = int // for demo purposes, but could be other type

// Sorts array 'a' using the bubble sort algorithm.
method bubbleSort(a: array<T>)
  modifies a
  ensures isSorted(a)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
    var n := a.Length; 
    while n  > 1 //external cycle/ right cycle
        invariant 0 <= n <= a.Length
        invariant multiset(a[..]) == multiset(old(a[..]))
        //invariant sorted(a,n, a.Length) -> necessario criar esta subrotina
        //less or equal 
    { 
      var newn := 0;
      var i := 1;
      while i < n //internal cycle, left cycle
      
       { 
          if (a[i-1] > a[i]) { 
              a[i-1], a[i] := a[i], a[i-1]; 
              newn := i;
          }
          i := i+1; 
      }
      n := newn;
    }
}

// Checks if array 'a' is sorted.
predicate isSorted(a: array<T>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}


// A simple test case (checked statically)
method testBubbleSort() {
    var a := new int[] [7, 4, 6, 3, 8, 9];
    assert a[..] == [7, 4, 6, 3, 8, 9];
    bubbleSort(a);
    assert isSorted(a);
    assert a[..] == [3, 4, 6, 7, 8, 9];
}