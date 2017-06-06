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

//  La Relacion tiene Primer Elemento
//pred PrimerElemento[r: Relacion, x: Elem]{
	//all y: r.elem | x->y in r.rel
//}

// PREGUNTAR SI ESTA BIEN ESCRITO ASI
pred PrimerElemento[r: Relacion, x: Elem]{
	some x: r.elem | all y: r.elem-x | x->y in r.rel
}


run PrimerElemento for 3 but 1 Relacion

//  La Relacion tiene Ultimo Elemento
pred UltimoElemento[r: Relacion, x: Elem]{
	all y: r.elem | y->x in r.rel
}

run UltimoElemento for 3 but 1 Relacion


//========
// Aserciones
//========

// Todo Orden Parcial es Orden Total
assert OrdenParcial_OrdenTotal {
	all r: Relacion | OrdenParcial[r] implies OrdenTotal[r] // => es equivalente a implies
}

check OrdenParcial_OrdenTotal

// Todo Orden Parcial tiene Primer Elemento
assert OrdenParcial_PrimerElemento {
	all r: Relacion | OrdenParcial[r] implies (some x : r.elem | PrimerElemento[r, x])
}

check OrdenParcial_PrimerElemento

// Todo Orden Total con Primer Elemento 'x' y ultimo elemento 'y' satisface x != y
//assert OrdenTotal_PU {
//	all r: Relacion | OrdenTotal[r] and (some x : r.elem | PrimerElemento[r, x]) and (some y : r.elem | UltimoElemento[r, y]) implies x != y
//}

//check OrdenTotal_PU

// La union de Ordenes Estrictos es un Orden Estricto
assert Union_OrdenesEstrictos {
	all r1, r2: Relacion | OrdenEstricto[r1]  and OrdenEstricto[r2] implies OrdenEstricto[r1 + r2] // => es equivalente a implies
}

check Union_OrdenesEstrictos

// La composicion de Ordenes Estrictos es un Orden Estricto
//assert Composicion_OrdenesEstrictos {
//	all r1, r2: Relacion | OrdenEstricto[r1]  and OrdenEstricto[r2] => OrdenEstricto[(r1).(r2)] // => es equivalente a implies
//}

//check Composicion_OrdenesEstrictos
