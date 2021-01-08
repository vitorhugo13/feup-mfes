sig Tree{
	root : lone Node 
}

sig Node{
	left, right: lone Node,
	value: one Int
}

--a
fun parent: Node->Node{
	{n1, n2: Node | n1->n2 in (left+right) implies n1 in left.n2 or n1 in right.n2}
}

pred wellFormedTree{
	--b
	all n: Node | some n.left + n.right implies n.left != n.right

	--c
	no iden & ^parent

	--d
	all n: Node - Tree.root | one n.parent

	--e
	all n: Node | all ln: leftValues[n], rn: rightValues[n] | n.value > ln.value and n.value < rn.value	

	--f
	all disj n1, n2: Node | n1.value != n2.value

	--g
	all n: Node | (#(leftValues[n])).minus[#rightValues[n]] =< 1
}

fun leftValues[n: Node]: set Node{
	{nodesOnSubTree[n.left]}
}

fun rightValues[n: Node]: set Node{
	{nodesOnSubTree[n.right]}
}

fun nodesOnSubTree[n: Node]: set Node{
	n.*left + n.*right
}

run {} for 6