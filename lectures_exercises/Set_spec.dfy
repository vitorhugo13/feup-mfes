/* 
* Specification, implementation and verification of a Set implemented with an array.
* Illustrates the usage of ghost variables and abstraction/refinement relations to better separate
* specification (interface) and implementation.
* This file contains only the interface specification and test cases.
* FEUP, MIEIC, MFES, 2019/20.
*/

class { :autocontracts } Set<T>{

    //variável de estado abstrata
    ghost var elems: set<T>; //ghost nao vai para código executavel

    constructor()
        ensures elems == {}



    method insert(x: T)
        ensures |elems| == old(|elems|) + 1
        ensures x in elems
        ensures old(elems) < elems //< significa ser subconjunto
        ensures elems == old(elems) + {x} //podemos substituir tudo anteriormente por isto



    method delete(x: T)
        requires x in elems
        ensures elems == old(elems) - {x}



    predicate method contains(x: T)
        ensures contains(x) <==> x in elems


    function method size(): nat //func. method para gerar codigo executavel
        ensures size() == |elems|

}

// A simple test scenario checked statically.
method testSet()
{
  var s := new Set();
  s.insert(2);
  s.insert(5);
  assert s.size() == 2;
  assert s.contains(2);
  assert s.contains(5);
  s.delete(2);
  assert s.size() == 1;
  assert s.contains(5);
  assert !s.contains(2);
  s.delete(5);
  assert !s.contains(5);
  assert s.size() == 0;
}