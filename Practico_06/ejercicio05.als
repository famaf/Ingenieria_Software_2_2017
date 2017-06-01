sig Elem{}

sig R{
	elem: set Elem,
	rel: elem -> elem
}

//  Predicados
pred Reflexiva[r:R]{
	(iden & (r.elem -> r.elem)) in r.rel
}

pred AntiReflexiva[r:R]{
	// Probar con not in, ie igual que Reflexivo pero con not in
	(iden & (r.elem -> r.elem)) in ((r.elem -> r.elem) - r.rel) // Lo que esta a la der es el complemento de R
}

pred Antisimetrica[r:R]{
	(r.rel) & (~(r.rel)) in (iden & (r.elem -> r.elem))
}

pred Transitiva[r:R]{
	((r.rel) . (r.rel)) in r.rel
}

pred Total[r:R]{
	(r.elem -> r.elem) in (r.rel + (~(r.rel)))
}

// Ordenes
pred Preorden[r: R]{
	Reflexiva[r]
	Transitiva[r]
}

run Preorden for 4  but 1 R, exactly 4 Elem

pred OrdenParcial[r: R]{
	Reflexiva[r]
	Antisimetrica[r]
	Transitiva[r]
}

run OrdenParcial for 5 but 1 R

pred OrdenTotal[r: R]{
	Reflexiva[r]
	Antisimetrica[r]
	Transitiva[r]
	Total[r]
	// Tambien se puede poner
	// OrdenTotal[r]
	// Transitiva[r]
}

run OrdenTotal for 5 but 1 R

pred OrdenEstricto[r: R]{
	AntiReflexiva[r]
	Antisimetrica[r]
	Transitiva[r]
}

run OrdenEstricto for 5 but 1 R

pred PrimerElemento[r: R, x:Elem]{
	all y:r.elem | x->y in r.rel
}

run PrimerElemento for 3 but 1 R
