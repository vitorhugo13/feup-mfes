type T = int

//Use binary search to find an appropriate position to insert a value 'x'
// in a sorted array 'a', so that it remains sorted.
method binarySearch(a: array<T>, x: T) returns(index: int)
    requires a.Length > 0
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] //menas array 'a' must be sorted
    ensures 0 <= index <= a.Length
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures index > 0 ==> a[index-1] <= x //position before index must be less or equal than x
    ensures index < a.Length ==> a[index] >= x //position after index must be greater or equal than x
{
    var low, high := 0, a.Length;
    while low < high
        decreases high - low
        invariant 0 <= low <= high <= a.Length
        invariant low > 0 ==> a[low-1] <= x
        invariant high < a.Length ==> a[high] >= x
    {
        var mid := low + (high - low) / 2;


        if{
            case a[mid] < x => low := mid + 1;
            case a[mid] > x => high := mid;
            case a[mid] == x => return mid;
        }
    }

    return low;
}

method testBinarySearch(){
   var a := new int[2] [1,3];
   var id0 := binarySearch(a, 0);
   assert id0 == 0;
   var id1 := binarySearch(a, 1);
   assert id1 in {0,1};
   var id2 := binarySearch(a, 2);
   assert id2 == 1;
   var id3 := binarySearch(a, 3);
   assert id3 in {1,2};
   var id4 := binarySearch(a,4);
   assert id4 == 2;
}
