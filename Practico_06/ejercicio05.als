sig Elem{}

sig Relacion{
	elem: set Elem,
	rel: elem -> elem
}


//========
// Predicados
//========

//  La Relacion es Reflexiva
pred Reflexiva[r: Relacion]{
	// r.elem -> r.elem : Universo Local
	(iden & (r.elem -> r.elem)) in r.rel
}

//  La Relacion es Antireflexiva
pred Antireflexiva[r: Relacion]{
	// Complemento de r : (r.elem -> r.elem) - r.rel
	// Probar con not in, ie igual que Reflexivo pero con not in
	(iden & (r.elem -> r.elem)) in ((r.elem -> r.elem) - r.rel) // Lo que esta a la der es el complemento de R
}

//  La Relacion es Antisimetrica
pred Antisimetrica[r: Relacion]{
	(r.rel) & (~(r.rel)) in (iden & (r.elem -> r.elem))
}

//  La Relacion es Transitiva
pred Transitiva[r: Relacion]{
	((r.rel) . (r.rel)) in r.rel
}

//  La Relacion es Total
pred Total[r: Relacion]{
	(r.elem -> r.elem) in (r.rel + (~(r.rel)))
}

//  La Relacion es un Preorden
pred Preorden[r: Relacion]{
	Reflexiva[r]
	Transitiva[r]
}

run Preorden for 4  but 1 Relacion, exactly 4 Elem

//  La Relacion es un Orden Parcial
pred OrdenParcial[r: Relacion]{
	Reflexiva[r]
	Antisimetrica[r]
	Transitiva[r]
}

run OrdenParcial for 5 but 1 Relacion

//  La Relacion es un Orden Total
pred OrdenTotal[r: Relacion]{
	Reflexiva[r]
	Antisimetrica[r]
	Transitiva[r]
	Total[r]
	// Tambien se puede poner
	// OrdenParcial[r]
	// Total[r]
}

run OrdenTotal for 5 but 1 Relacion

//  La Relacion es un Orden Estricto
pred OrdenEstricto[r: Relacion]{
	Antireflexiva[r]
	Antisimetrica[r]
	Transitiva[r]
}

run OrdenEstricto for 5 but 1 Relacion

//  La Relacion tiene Primer Elemento - VERSION 1
pred PrimerElemento_v1[r: Relacion, x: Elem]{
	OrdenParcial[r]
	all y: r.elem | x->y in r.rel
}

run PrimerElemento_v1 for 3 but 1 Relacion

//  La Relacion tiene Primer Elemento - VERSION 2
pred PrimerElemento_v2[r: Relacion]{
	OrdenParcial[r]
	some x: r.elem | all y: r.elem | x->y in r.rel
}


//  La Relacion tiene Ultimo Elemento - VERSION 1
pred UltimoElemento_v1[r: Relacion, x: Elem]{
	OrdenParcial[r]
	all y: r.elem | y->x in r.rel
}

run UltimoElemento_v1 for 3 but 1 Relacion

//  La Relacion tiene Ultimo Elemento - VERSION 1
pred UltimoElemento_v2[r: Relacion]{
	OrdenParcial[r]
	some x: r.elem | all y: r.elem | y->x in r.rel
}


//========
// Aserciones
//========

// Todo Orden Parcial es Orden Total
assert OrdenParcial_OrdenTotal {
	all r: Relacion |
	OrdenParcial[r] implies
	OrdenTotal[r]
}

check OrdenParcial_OrdenTotal

// Todo Orden Parcial tiene Primer Elemento
assert OrdenParcial_PrimerElemento {
	//all r: Relacion | OrdenParcial[r] implies (some x: r.elem | PrimerElemento_v1[r, x])
	//all r: Relacion | OrdenParcial[r] implies PrimerElemento_v2[r] // Usando VERSION 2
	all r: Relacion |
	some x: r.elem |
	OrdenParcial[r] implies
	PrimerElemento_v1[r, x]
}

check OrdenParcial_PrimerElemento

// Todo Orden Total con Primer Elemento 'x' y ultimo elemento 'y' satisface x != y
assert OrdenTotal_PU {
	all r: Relacion |
	some x, y: r.elem |
	(OrdenTotal[r]  and
	PrimerElemento_v1[r, x] and
	UltimoElemento_v1[r, y]) implies
	(x != y)
}

check OrdenTotal_PU

// La union de Ordenes Estrictos es un Orden Estricto
assert Union_OrdenesEstrictos {
	all r1, r2: Relacion |
    (OrdenEstricto[r1]  and
    OrdenEstricto[r2]) implies

    (all r3: Relacion |
     (r3.elem = r1.elem + r2.elem and
      r3.rel = r1.rel + r2.rel) implies
      OrdenEstricto[r3])
}

check Union_OrdenesEstrictos for 2 but 3 Relacion

// La composicion de Ordenes Estrictos es un Orden Estricto
assert Composicion_OrdenesEstrictos {
	all r1, r2: Relacion |
	(OrdenEstricto[r1]  and
     OrdenEstricto[r2]) implies

	(all r3: Relacion |
	 (r3.elem = r1.elem + r2.elem and
	  r3.rel = (r1.rel) . (r2.rel)) implies
     OrdenEstricto[r3])
}

check Composicion_OrdenesEstrictos for 2 but 3 Relacion
