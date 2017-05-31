sig Elem{}

sig R{
	elem: set Elem,
	rel: elem -> elem
}


pred Preorden[r: R]{
	(iden & (r.elem-> r.elem)) in r.rel // Reflexivo
	((r.rel) . (r.rel)) in r.rel // Transitivo
}


run Preorden for 5 but 1 R
