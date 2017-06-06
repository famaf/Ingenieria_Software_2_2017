module practico6/ ej13

sig Node {}

sig Tree {
	node: set Node,
	root: one node,
	edge: node one -> (node - root)  // one para que no llegue a un nodo por dos nodos diferentes
}{
	some edge // No es vacio
no (iden & ^edge)
}


pred show {}
run show for 3 but exactly 1 Tree

pred connected[t: Tree] {
	all n: t.node | some n1, n2: t.node | n1->n in t.edge and n->n2 in t.edge
}

pred acyclic[t: Tree] {
//	
}







