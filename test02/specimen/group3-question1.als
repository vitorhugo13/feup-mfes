sig Tree{
	root: lone Node
}

sig Node{
	left, right: lone Node,
  	value: one Int,
  	parentNode: Node
}

fun parent(n: Node): Node->Node{ // (a)
 	parentNode + n->((left :> n).n + (right :> n).n) //restringir o range da relação right e left ao node n, deste modo a função parent irá retornar os nós nos quais n está à direita/esquerda aka o meu pai
}

pred wellFormedTree{
  all n: Node | (#n.right > 0 or #n.left > 0) implies n.right != n.left //(b)
  all n: Node | n not in n.^parentNode //(c)
  all nd: Node - Tree.root | one nd.parentNode //(d)
  all node: Node | (all nl: node.^left | node.value > nl.value) and (all nr: node.^right | node.value < nr.value)// (e)
  all n1, n2: disj Node | n1.value != n2.value // (f)
  all node: Node | #(node.^left)- #(node.^right) =< 1
}

run {}

//aloy4fun: http://alloy4fun.inesctec.pt/ooRhAcjMtz3on9FdJ