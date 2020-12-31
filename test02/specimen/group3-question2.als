open util/ordering[Time2] // (a)

sig Time2{} // (a)

one sig List{
	head: Node->Time2  // (b)
}

sig Node{
	next: Node->Time2, // (b)
  	value: Int
}

fact{ // (b) restrictions as facts 
 	all l: List | lone l.head
  	all n: Node | lone n.next
}

pred init(t: Time2){
	no List.head //(c)
}

pred delete(t, t2: Time2, n: Node, l: List){ //(d)
  //pre-condition
  n in (l.head.t).^(next.t)
  
  //delete
  (l.head.t2).^(next.t2) = (l.head.t).^(next.t) - n
  
  //post-conditions
  n not in (l.head.t2).^(next.t2)
  all n: (l.head.t2).^(next.t2), n2: (l.head.t).^(next.t) - n | (n.next).Time2 = (n2.next).Time2
}
 
pred insert(n: Node){ // (e)
  //assume insert method is done
}

fact traces{ // (e)
    init[first]
    all t: Time2 - last | let t2 = t.next|
    	some n: Node, l: List | delete[t,t2,n,l] or insert[n]
}

assert checkOrder{ // (f)
  all l: List | (l.head).Time2.value =< (l.head).Time2.next.Time2.value //head <= next  
  all n: (List.head.Time2).^(next.Time2) |  n.value =< n.next.Time2.value //element <= element.next

}

check checkOrder for 4 but 6 Time2 //(f)

run {} for 4 but 6 Time2

