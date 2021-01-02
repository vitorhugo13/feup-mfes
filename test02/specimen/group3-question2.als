// Note: Some auxiliar functions, such as, elements and previousElement are authored by David Silva (https://github.com/daviddias99)

open util/ordering[Time] // (a)

sig Time{} // (a)

one sig List{
	head: Node lone ->Time  // (b)
}

sig Node{
	next: Node lone-> Time, // (b)
  value: Int
}

pred init(t: Time){
	no List.head //(c)
}

//retrieves set of Nodes after n
fun elements(n: Node, t: Time): set Node{
  {(n.*(next.t))}
}

//retrieves element before n
fun previousElement(n: Node, t: Time): Node{
  {(next.t).n}
}

/*
pred delete(t, t2: Time, n: Node, l: List){ //(d)
  //pre-condition
  n in (l.head.t).^(next.t)
  
  //delete
  (l.head.t2).^(next.t2) = (l.head.t).^(next.t) - n
  
  //post-conditions
  n not in (l.head.t2).^(next.t2)
  all n: (l.head.t2).^(next.t2), n2: (l.head.t).^(next.t) - n | (n.next).Time = (n2.next).Time
}
*/

//using auxiliar functions
pred delete2(t,t2: Time, n: Node, l: List){
  //pre-condition (n must be in List before being removed)
  n in elements[List.head.t,t]
  n = l.head.t implies l.head.t2 = n.next.t else previousElement[n,t].next.t2 = n.next.t //delete n

  //post-condition
  n not in elements [List.head.t2, t2]
  all disj n1, n2: Node - n | n2 in elements[n1,t] implies n2 in elements[n1, t2]
}

pred insert(n: Node){ // (e)
  //assume insert method is done
}

fact traces{ // (e)
    init[first]
    all t: Time - last | let t2 = t.next|
    	some n: Node, l: List | delete2[t,t2,n,l] or insert[n]
}

fact sorted{ // (f)
  all time: Time | all disj n1, n2: Node | n2 in elements[n1,time] implies n2.value > n1.value
}

assert checkOrder{ // (f)
  all time: Time | all disj n1, n2: Node | n2 in elements[n1,time] implies n2.value > n1.value
}

check checkOrder for 4 but 3 Time //(f)

run {} for 4 but 6 Time

