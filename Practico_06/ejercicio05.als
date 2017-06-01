sig Elem{}

sig R{
	elem: set Elem,
	rel: elem -> elem
}

//  Predicados
pred Reflexiva[r:R]{
	(iden & (r.elem -> r.elem)) in r.rel
}

//pred NoReflexiva[r:R]{
	//((iden & (r.elem -> r.elem)) & (r.rel)) in none // Como hago que sea no reflexiva
//}

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

run Preorden for 5 but 1 R

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
}

run OrdenTotal for 5 but 1 R

// Hacer no Reflexivo
pred OrdenEstricto[r: R]{
//	NoReflexiva[r])
	Antisimetrica[r]
	Transitiva[r]
}

run OrdenEstricto for 5 but 1 R
