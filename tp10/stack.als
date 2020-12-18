open util/ordering[StackState] //biblioteca para criar o conjunto ordenado (posições do stack state ordenados)

sig Element {}

sig StackState {
    elements: seq Element //conjunto ordenado de elements
}{
    //
}

abstract sig Event {
    pre, post: disj StackState
}{
    // constraints that should hold for each Event
}

/*

fact firstState {
    // constraints for the first StackState
  
  	//inicialmente stack vazia
  	first.elements.isEmpty
  	
}
*/


//predicado init substitui o fact firstState
pred init [a: StackState]{
 	a.elements.isEmpty
}


fact trace {
     
    // relate all `StackState`s and `Event`s 
  
  	//initial state
  	init [first] //se usar o facto inves do predicado nao preciso disto aqui
  
  	//post-conditions
  	all s: StackState - last | let s1 = s.next |
      	some e: Event { 
        	e.pre = s
			e.post = s1
      	}
}

sig Push extends Event {
    value: Element
}{
  	
    // -- model pushing by relating `pre`, `post`, and `value`
  	value = post.elements.first
  	
  	// same as below: post.elements = pre.elements.insert [0, value] 
  	post.elements.rest = pre.elements
}

sig Pop extends Event {
    //
  	value: one Element //valor a ser removido do topo da stack
}{
    not pre.elements.isEmpty //stack must not be empty
  	value = pre.elements.first
  	post.elements = pre.elements.rest 
  	
}

assert popThenPush {
    // Pop followed by a Push of the same element
  
  	//pre.s1 dá todos os eventos antes de s1(state1). 
  	//no entanto esses eventos podem ser push ou pop, 
  	//para restringir a Pop fazemos pre.s1 <: Pop
  
  	all s: StackState - last | let s1 = s.next |
  		(some pre.s1 <: Push and some pre.s <: Pop) implies (pre.s <: Pop).value = (pre.s1 <: Push).value
}
check popThenPush


fact InitEqualsFinal {
	first.elements.isEmpty
  	last.elements.isEmpty
}
// para isto acontecer a stack tem de estar vazia
assert sameNumberPushesPops {
    #Pop = #Push
}
check sameNumberPushesPops


assert noPopFromEmpty {
    // nao ha nenhum evento Pop, em que pre esteja vazio
  	no popE: Pop | popE.pre.elements.isEmpty
}
check noPopFromEmpty

run {}