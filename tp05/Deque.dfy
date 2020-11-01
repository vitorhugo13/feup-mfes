type T = int // for demo purposes, but could be another type
 
class {:autocontracts} Deque {
    // (Private) concrete state variables 
    const list: array<T>; // circular array, from list[start] (front) to list[(start+size-1) % list.Length] (back) 
                             
    var start : nat; 
    var size : nat;
 
    // (Public) ghost variables used for specification purposes only
    ghost var elems: seq<T>;  // front at head, back at tail
    ghost const capacity: nat; 

    constructor (capacity: nat) 
        requires capacity > 0
        ensures elems == [] && this.capacity == capacity
    {
        list := new T[capacity];
        start := 0;
        size := 0;

        //inicializar variaveis abstratas
        //c)
        elems := [];
        this.capacity := capacity;
    }
 
  //(i) the consistency of the concrete state variables; 
  //(ii) the consistency between the concrete and abstract (ghost) state variables (abstraction relation).
    predicate Valid(){

        //(i)
        size <= list.Length 
        && 0 <= start < list.Length //como start é nat , >0 ja esta implicito 

        //(ii)
        && capacity == list.Length
        && elems == if start + size <= list.Length //não dá volta
                    then list[start..start+size] 
                    else list[start..] + list[.. (start + size) - list.Length]
        //&& elems == (list[..]+list[..])[start..start+size] -> alternativa ao if
    }

    predicate method isEmpty() 
        ensures isEmpty() <==> |elems| == 0
    {
        size == 0
    }
    
    predicate method isFull() 
        ensures isFull() <==> |elems| == capacity 
    {
        size == list.Length
    }
 
    function method front() : T 
        requires !isEmpty()
        ensures front() == elems[0]
    {
        list[start]
    }
 
    function method back() : T 
        requires !isEmpty()
        ensures back() == elems[ |elems| - 1]
    {
        list[(start + size - 1) % list.Length] 
    }
    
    method push_back(x : T) 
        requires !isFull()
        ensures  elems == old(elems) + [x]

    {


        // c) needed to add this if...else 
        if start + size + 1 <= list.Length {
            list[start + size] := x;
        }
        else{
            list[(start + size) % list.Length] := x;
        }

        size := size + 1;

        //C)
        elems := elems + [x]; //concatenar com o +
    }
 
    method pop_back() 
        requires !isEmpty()
        ensures elems == old(elems[..|elems| - 1])
    {
        size := size - 1;

        elems := elems[..size];
    }
 
    method push_front(x : T) 
        requires !isFull()
        ensures elems == [x] + old(elems)
    {
        if start > 0 {
            start := start - 1;
        }
        else {
            start := list.Length - 1;
        }
        list[start] := x;
        size := size + 1;

        elems := [x] + elems;
    }    
 
    method pop_front() 
        requires !isEmpty()
        ensures elems == old(elems[1..])
    {
        if start + 1 < list.Length {
            start := start + 1;
        }
        else {
            start := 0;
        }
        size := size - 1;

        elems := elems[1..];
    } 
}

//e) Fazendo com esta sugestao fica mais facil
 
// A simple test scenario.
method testDeque()
{
    var q := new Deque(3);
    assert q.isEmpty();
    q.push_front(1);
    assert q.front() == 1;
    assert q.back() == 1;
    q.push_front(2);
    assert q.front() == 2;
    assert q.back() == 1;
    q.push_back(3);
    assert q.front() == 2;
    assert q.back() == 3;
    assert q.isFull();
    q.pop_back();
    assert q.front() == 2;
    assert q.back() == 1;
    q.pop_front();
    assert q.front() == 1;
    assert q.back() == 1;
    q.pop_front();
    assert q.isEmpty();
}
