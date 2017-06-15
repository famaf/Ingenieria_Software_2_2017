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

pred Grafo_Arbol[g: Grafo]{
    Aciclico[g]
    all x, y: g.nodos | (x->y) in g.aristas implies !(some z: g.nodos | (z->y) in g.aristas)
}

run Grafo_Arbol for 3 but 1 Grafo
