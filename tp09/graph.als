/* 
Each node as a set of outgoing edges, representing a directed graph without multiple edged.
*/
sig Node {
	adj : set Node
}

/*
The graph is undirected, ie, edges are symmetric.
http://mathworld.wolfram.com/UndirectedGraph.html
*/
pred undirected {
	all n1, n2: Node | n1->n2 in adj implies n2->n1 in adj //FOL
  	//all n1, n2: Node | n1 in n2.adj implies n2 in n1.adj //Mistura de FOL e RL
  	//adj = ~adj (lógica relacional -  ~ = transposta)
}

run undirected {
  undirected
}

/*
The graph is oriented, ie, contains no symmetric edges.
http://mathworld.wolfram.com/OrientedGraph.html
*/
pred oriented {
	all n1, n2: Node | n1->n2 in adj implies n2->n1 not in adj //FOL
  	//no adj & ~adj (RL)
}

/*
The graph is acyclic, ie, contains no directed cycles.
http://mathworld.wolfram.com/AcyclicDigraph.html
*/
pred acyclic {
  	//a partir de um nó não posso chegar ao nó (qualquer nó)
  	//para ver as travessias de um grafo usar fecho transitivo
  
  	all n: Node | n not in n.^adj
  	//no iden & ^ adj

}

/*
The graph is complete, ie, every node is connected to every other node.
http://mathworld.wolfram.com/CompleteDigraph.html
*/
pred complete {
	//all n1, n2: Node | n1 in n2.adj
	//all n: Node | n.adj = Node
  	//all n1, n2 : Node | n1 -> n2 in adj
	adj = Node->Node	
  	//no n1,n2 : Node | n1 !in n2.adj
}

/*
The graph contains no loops, ie, nodes have no transitions to themselves.
http://mathworld.wolfram.com/GraphLoop.html
*/
pred noLoops {
	all n : Node | n not in n.adj
}

/*
The graph is weakly connected, ie, it is possible to reach every node from every node ignoring edge direction.
http://mathworld.wolfram.com/WeaklyConnectedDigraph.html
*/
pred weaklyConnected {
	//all disj n1, n2: Node | n2 in n1.^(adj + ~adj)  
	Node->Node in *(adj + ~adj) //uniao dos adj com transposta de adj para ignorar edge direction
}

/*
The graph is strongly connected, ie, it is possible to reach every node from every node considering edge direction.
http://mathworld.wolfram.com/StronglyConnectedDigraph.html
*/
pred stonglyConnected {
  	//parecido ao anterior, mas a direção da aresta irá ser considerada
	// all n1, n2: Node | n2 in n1.*adj
	Node->Node - iden in ^adj 
  	//all disj n1, n2: Node | n1 in n2.^adj
}

/*
The graph is transitive, ie, if two nodes are connected through a third node, they also are connected directly.
http://mathworld.wolfram.com/TransitiveDigraph.html
*/
pred transitive {
	all n1, n2, n3: Node | n1->n2 in adj and n2->n3 in adj implies n1->n3 in adj
	//adj = ^adj
  	//adj.adj in adj
}

run{}