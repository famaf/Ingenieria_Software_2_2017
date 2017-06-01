sig Nodo{}

sig Grafo{
	nodos: set Nodo,
	aristas: nodos -> nodos
}

pred Aciclico[g:Grafo]{
	no(iden & ^(g.aristas))
	//(iden & ^(g.aristas)) = (none) NO COMPILA ESTO
}

run Aciclico for 4 but 1 Grafo

pred NoDirigido[g:Grafo]{
    (g.aristas) = ~(g.aristas)
}

run NoDirigido for 4

pred FConexo[g:Grafo]{
        ^(g.aristas) = g.nodos -> g.nodos
}

run FConexo for 4
// run FConexo for 6 but 1 Grafo, exactly 3 Nodo

pred ConexoNodos3[g:Grafo]{
	FConexo[g]
	#g.nodos = 3
}

//pred Conexo[g: Grafo]{
	//g.aristas = g.nodos -> g.nodos
       //g.aristas = ^(g.aristas)
	//g.aristas = 
//}

//run Conexo for 4 but 1 Grafo



