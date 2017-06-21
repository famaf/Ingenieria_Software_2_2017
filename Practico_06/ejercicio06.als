sig Estado{}

sig Label{}

sig LTS{
	estados: set Estado,
	label: set Label,
	transiciones: label->estados->estados,
	init: one estados
}{
    // Todos los estados de un LTL son alcanzables desde su estado inicial
	init . (^(transiciones[Label])) = estados
	//init.((^(Label)).(transiciones)) = estados
}

one sig Tau extends Label{} // Un solo Tau

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


pred Simulacion_Debil[r: Estado -> Estado, t1: LTS]{
	r in (t1.estados->t1.estados)
	~(r) . (t1.transiciones[Tau]) in *(t1.transiciones[Tau]) . ~(r)
	~(r) . (t1.transiciones[Label]) in (*(t1.transiciones[Tau]) . (t1.transiciones[Label]) . *(t1.transiciones[Tau])) . ~(r)
}

run Simulacion_Debil

pred Simulacion_Debil_Inversa[r: Estado -> Estado, t1: LTS]{
	r in (t1.estados->t1.estados)
	r . (t1.transiciones[Tau]) in *(t1.transiciones[Tau]) . r
	r . (t1.transiciones[Label]) in (*(t1.transiciones[Tau]) . (t1.transiciones[Label]) . *(t1.transiciones[Tau])) . r
}

run Simulacion_Debil_Inversa

pred Bisimulacion_Debil[r: Estado -> Estado, t1: LTS]{
	r in (t1.estados->t1.estados)
	Simulacion_Debil[r, t1]
	Simulacion_Debil_Inversa[r, t1]
}

run Bisimulacion_Debil

//========
// Aserciones
//========

assert Bisimulacion_Simulacion{
	all lts: LTS | all r: (Estado->Estado) | Bisimulacion[r, lts] implies Simulacion[r, lts]
}

assert Bisimulacion_BisimulacionDebil{
	all lts: LTS | all r: (Estado->Estado) | Bisimulacion[r, lts] implies Bisimulacion_Debil[r, lts]
}

check Bisimulacion_Simulacion

check Bisimulacion_BisimulacionDebil
