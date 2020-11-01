// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
    modifies a 
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) ==  multiset(old(a[..]))
{
    var i := 0;
    while i < a.Length 
        invariant 0 <= i <= a.Length
        invariant isSorted(a, 0, i)
        invariant multiset(a[..]) ==  multiset(old(a[..]))
    {
        var j := i;
        while j > 0 && a[j-1] > a[j] 
            invariant 0 <= j <= i
            invariant multiset(a[..]) ==  multiset(old(a[..]))
            //invariant isSorted(a, 0, j) && isSorted(a,j, i + 1) && isSortedExcluding(a, 0, i + 1, j) ou
            invariant forall l, r :: 0 <= l < r <= i &&  r!= j ==> a[l] <= a[r]
        {
            a[j-1], a[j] := a[j], a[j-1];
            j := j - 1;
        }
        i := i + 1;
    }
}

// Simple test case to check the postcondition
method testInsertionSort() {
  var a := new int[] [ 9, 4, 3, 6, 8];
  assert a[..] == [9, 4, 3, 6, 8];
  insertionSort(a);
  assert a[..] == [3, 4, 6, 8, 9];
}

predicate isSorted(a: array<int>, from: nat, to:nat)
    requires 0 <= from <= to <= a.Length
    reads a
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}


predicate isSortedExcluding(a: array<int>, from: nat, to:nat, k:nat)
    requires 0 <= from <= to <= a.Length
    reads a
{
    forall i, j :: from <= i < j < to && i !=k && j != k ==> a[i] <= a[j]
}

/* OUTRO PROF
predicate isSorted(a: array<int>, low: nat, high: nat)

  reads a

  requires 0 <= low <= high <= a.Length

{

    forall i, j :: low <= i < j < high ==> a[i] <= a[j]

}

// Sorts array 'a' using the insertion sort algorithm.

method insertionSort(a: array<int>)

    modifies a

    ensures multiset(a[..]) == multiset(old(a[..])) // same elements

    ensures isSorted(a, 0, a.Length) // sorted

{

    var i := 0;

    while i < a.Length

        decreases a.Length - i

        invariant 0 <= i <= a.Length

        invariant multiset(a[..]) == multiset(old(a[..]))

        invariant isSorted(a, 0, i)

    {

        var j := i;

        while j > 0 && a[j-1] > a[j]

            decreases j

            invariant 0 <= j <= i        

            invariant multiset(a[..]) == multiset(old(a[..]))

            invariant  forall m, n :: 0 <= m <= n <= i && m != j && n != j ==> a[m] <= a[n] // all elements sorted if a[j] is removed

            invariant isSorted(a, j, i + 1) // all the elements at and after j are sorted

        {

            a[j-1], a[j] := a[j], a[j-1];

            j := j - 1;

        }

        i := i + 1;

    }

}

// Simple test case to check the postcondition

method testInsertionSort() {

  var a := new int[5] [ 9, 4, 3, 6, 8];

  assert a[..] == [9, 4, 3, 6, 8];

  insertionSort(a);

  assert a[..] == [3, 4, 6, 8, 9];

}
*/
