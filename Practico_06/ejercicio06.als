sig Estado{}

sig Label{}

sig LTS{
	estados: set Estado,
	label: set Label,
//	transiciones: Label->Estado->Estado
	transiciones: label->estados->estados,
	init: estados
}{
    // Todos los estados de un LTL son alcanzables desde su estado inicial
	init . (^(transiciones[Label])) = estados
	//init.((^(Label)).(transiciones)) = estados
}


//========
// Predicados
//========

// R simulacion
pred Simulacion[r: Estado -> Estado, t1: LTS]{
	r in (t1.estados->t1.estados)
	~(r) . (t1.transiciones[Label]) in (t1.transiciones[Label]) . ~(r)
}

run Simulacion

// R^{-1} simulacion
pred Simulacion_Inversa[r: Estado -> Estado, t1: LTS]{
	r in (t1.estados->t1.estados)
	r . (t1.transiciones[Label]) in (t1.transiciones[Label]) . r
}

run Simulacion_Inversa

// R bisimulacion
pred Bisimulacion[r: Estado -> Estado, t1: LTS]{
	r in (t1.estados->t1.estados)
	Simulacion[r, t1]
	Simulacion_Inversa[r, t1]
}

run Bisimulacion


//========
// Aserciones
//========

assert Bisimulacion_Simulacion{
	all lts: LTS | all r: (Estado->Estado) | Bisimulacion[r, lts] implies Simulacion[r, lts]
}

check Bisimulacion_Simulacion
