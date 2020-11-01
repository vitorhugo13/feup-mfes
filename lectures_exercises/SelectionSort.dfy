/* 
* Formal verification of the selection sort algorithm in Dafny.
*/

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>) 
    //clausula para modificar os arrays
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) ==  multiset(old(a[..])) //new_a(em sequencia) is permutation of old_a(o inicial)
{
    var i := 0; 
    while i < a.Length - 1 
    //ver variant e invariant na soluçao(moodle)
    {
        var j := findMin(a, i, a.Length); // minimum in remaining subarray
        a[i], a[j] := a[j], a[i]; // swap
        i := i + 1;
    }
}

// Finds the position of a miminum value in a non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat) 
    requires 0 <= from < to <= a.Length
    ensures from <= index < to 
    //ensures forall k :: from <= k < to ==> a[ĸ] >= a[index] //qql que seja k dentro do intervalo ... então..
    //se descomentar a linha de cima da erro nao sei pq e deixa de analisar
{
    var i := from + 1;
    index := from; // position of min up to position i (excluded)
    while i < to 
        invariant from + 1 <= i <= to
        invariant from <= index < to
        //invariant forall k :: from <= k < to ==> a[ĸ] >= a[index]
        decreases to - i
    {
        if a[i] < a[index] {
            index := i;
        }
        i := i + 1;
    }
}

method testSelectionSort() {
  var a := new real[5] [9.0, 4.0, 6.0, 3.0, 8.0];
  assert a[..] == [9.0, 4.0, 6.0, 3.0, 8.0];
  selectionSort(a);
  assert a[..] == [3.0, 4.0, 6.0, 8.0, 9.0];
}

method testFindMin() {
  var a := new real[5] [9.0, 5.0, 6.0, 4.0, 8.0];
  assert a[..] == [9.0, 5.0, 6.0, 4.0, 8.0];
  var m := findMin(a, 0, 5);
  assert a[3] == a[m] == 4.0;
  assert m == 3;
}