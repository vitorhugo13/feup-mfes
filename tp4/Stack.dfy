type T = int // to allow doing new T[capacity], but can be other type 
 
class {:autocontracts} Stack
{
    const elems: array<T>; // immutable (pointer)
    var size : nat; // used size
 
    constructor (capacity: nat)
        requires capacity > 0
        ensures size == 0 && elems.Length ==capacity
    {
        elems := new T[capacity];
        size := 0; 
    }
 
    //class invariant
    predicate Valid()
        reads this
    {
        size <= elems.Length
    }
 
    predicate method isEmpty()
    {
        size == 0
    }
 
    predicate method isFull()
    {
        size == elems.Length
    }
 
    method push(x : T)

        //requires size < elems.Length -> também poderia ser usado - equivalentes
        requires ! isFull() 
        ensures size == old(size) + 1 //redundante com as coisas em choose 1
        ensures elems[old(size)] == x //redundante com as coisas em choose 1

        //choose 1
        ensures forall i :: 0 <= i < old(size) ==> elems[i] == old(elems[i])
        ensures old(elems[0..size]) == elems[..old(size)]
        ensures old(elems[..size]) + [x] == elems[..size]
    {
        elems[size] := x;
        size := size + 1;
    }
 
    function method top(): T
        requires ! isEmpty()
    {
        assert 0 <= size - 1 < elems.Length;
         elems[size-1]
    }
    
    method pop() 
        requires ! isEmpty()
        ensures elems[..size] == old(elems[..size-1])
    {
         size := size-1;
    }
}
 
// A simple test case.
method Main()
{
    var s := new Stack(3);
    assert s.isEmpty();
    s.push(1);
    s.push(2);
    s.push(3);
    assert s.top() == 3;
    assert s.isFull();
    s.pop();
    assert s.top() == 2;
    print "top = ", s.top(), " \n";
}
