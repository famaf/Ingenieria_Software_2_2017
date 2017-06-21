sig Nodo{}

sig Grafo{
    nodos: set Nodo,
    aristas: nodos -> nodos
}


//========
// Predicados
//========

// El Grafo es Aciclico
pred Aciclico[g: Grafo]{
    no(iden & ^(g.aristas))
}

// Cada nodo tiene un unico padre
pred PadreUnico[g: Grafo]{
	//all x, y: g.nodos | (x->y) in g.aristas implies !(some z: g.nodos | (z->y) in g.aristas and x!=z)
	(g.aristas . ~(g.aristas)) in (iden & (g.nodos->g.nodos))
}

// El arbol tiene una unica raiz
pred RaizUnica[g: Grafo]{
	some x: Nodo | all y: Nodo | (x->y) in *(g.aristas)
}

// El Grafo es un arbol
pred Grafo_Arbol[g: Grafo]{
    Aciclico[g]
    PadreUnico[g]
    RaizUnica[g]
}

run Grafo_Arbol for 5 but 1 Grafo
