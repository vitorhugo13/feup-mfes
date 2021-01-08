open util/ordering[Time] --a

sig Time {} --a
one sig List{
	head: Node lone -> Time --b
}

sig Node{
	next: Node lone -> Time, --b
	value: Int
}

--c
pred init[t: Time]{
	no List.head.t
}


--d
fun nodeBefore[n: Node, t: Time] : Node{
	{(next.t).n}
}

fun nodesAfter[n: Node, t: Time]: set Node{
	{(n.*(next.t))}
}

pred delete[n: Node, t, t2: Time]{
	--pre-conditions
	n in nodesAfter[List.head.t, t]
	--post-conditions
	(n = List.head.t) implies (List.head.t2 = n.next.t) else (nodeBefore[n,t].next.t = n.next.t)
	nodesAfter[List.head.t2, t2] = nodesAfter[List.head.t, t] - n
	all disj n1, n2: Node - n | n1 in nodesAfter[n2, t] implies n1 in nodesAfter[n2, t2]
	
}
--e
fact Traces{
	all t: Time - last | let t2= t.next |
		some n: Node | delete[n, t, t2] or insert[n]
}

pred insert[n: Node]{
	--assume insert is given
}

--f
fact listSorted{
	all disj n, n2: Node, t: Time | n in nodesAfter[n2, t] implies n.value > n2.value
}

run {} for 6 but 4 Time