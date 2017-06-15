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

pred PadreUnico[g: Grafo]{
	(g.aristas . ~(g.aristas)) in (iden & (g.nodos->g.nodos))
}

pred RaizUnica[g: Grafo]{
	some x: Nodo | all y: Nodo | (x->y) in *(g.aristas)
}

pred Grafo_Arbol[g: Grafo]{
    Aciclico[g]
	PadreUnico[g]
	RaizUnica[g]
    //all x, y: g.nodos | (x->y) in g.aristas implies !(some z: g.nodos | (z->y) in g.aristas)

}

run Grafo_Arbol for 5 but 1 Grafo
