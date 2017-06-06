module practico6/ directedGraph


sig Vertex {}

sig Graph {
	arrow: Vertex -> Vertex
}{
	not no arrow
}


pred Acyclic[g: Graph] {
	no ^(g.arrow) & iden
}
//run Acyclic for 3

pred NoDirected[g: Graph] {
	g.arrow = ~g.arrow
}
//run NoDirected for 3

pred StronglyConvex[g: Graph]{
	^g.arrow = Node -> Node
}

pred Convex[g: Graph] {
	^(g.arrow + ~g.arrow) = Node -> Node
}

pred OneStronglyConvex[g: Graph] {
	some g2: Graph | g2.arrow in g.arrow and StronglyConvex[g2]
}

pred OneConvex{
	some g2: Graph | g2.arrow in g.arrow and Convex[g2]
}


assert A_Acyclic {
	all g: Graph | Acyclic[g]
}
//check A

