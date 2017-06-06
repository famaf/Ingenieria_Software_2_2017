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
	// Otra Forma
	//(iden & ^(g.aristas)) = (none -> none)
}

run Aciclico for 4 but 1 Grafo

// El Grafo es No Dirigido
pred NoDirigido[g: Grafo]{
    g.aristas = ~(g.aristas)
}

run NoDirigido for 4

// El Grafo es Fuertemente
pred FConexo[g: Grafo]{
	// g.nodos -> g.nodos : Universo local
        ^(g.aristas) = g.nodos -> g.nodos
}

run FConexo for 4 
// Otra forma: run FConexo for 6 but 1 Grafo, exactly 3 Nodo

pred FConexoNodos3[g: Grafo]{
	FConexo[g]
	#g.nodos = 3
}

// El Grafo es Conexo
pred Conexo[g: Grafo]{
	// g.nodos -> g.nodos : Universo local
	^(g.aristas + ~(g.aristas)) = g.nodos -> g.nodos
}

run Conexo for 4 but 1 Grafo

// Grafo Conexo, Sin Identidad y con 2 nodos
pred SinIdentidad[g: Grafo]{
	Conexo[g]
	g.aristas = g.aristas - iden
	#g.nodos =2
}

run SinIdentidad for 2 but 1 Grafo
