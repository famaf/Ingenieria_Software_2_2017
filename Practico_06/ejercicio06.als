sig Estado{}

sig Label{}

sig LTS{
	estados: set Estado,
	label: set Label,
//	transiciones: Label -> Estado -> Estado
	transiciones: label -> estados -> estados,
	init: estados
}{
	init . (^(transiciones[Label])) = estados
	//init.((^(Label)).(transiciones)) = estados
}

// Todos los estados de un LTL son alcanzables desde su estado inicial
//fact{all s.LTL.estados |  some a.Label | s}

// R simulacion
pred Simulacion[r: Estado -> Estado, t1: LTS]{
	r in t1.estados -> t1.estados
	~(r) . (t1.transiciones[Label]) in (t1.transiciones[Label]) . ~(r)
}

run Simulacion

// R^{-1} simulacion
//pred 1_Simulacion[r: Relacion, t1, t2: Transiciones]{}

// R bisimulacion
//pred Bisimulacion[r: Relacion, t1, t2: Transiciones]{}
