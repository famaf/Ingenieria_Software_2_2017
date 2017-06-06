module practico6/ LTS


sig State {}

sig Label {}

sig Graph {
	trans: State -> Label -> State
//	trans: State -> State
}

sig Relation {
	rel: State -> State
}


fact reachability {
	//one s0: State | some l: Label | all sN: State | s0->l->sN in Graph.trans
	//some s0: State | all sN: State | s0->sN in Graph.trans
}


pred Simulacion[g1, g2: Graph, r: Relation] {
	(~(r.rel)).(g1.trans) in (g2.trans).(~(r.rel))
}

pred BiSimulacion[g1, g2: Graph, r: Relation] {
	(~(r.rel)).(g1.trans) in (g2.trans).(~(r.rel))
	(~(r.rel)).(g2.trans) in (g1.trans).(~(r.rel))
}

pred biSimulacionDebil[g1, g2: Graph, r: Relation] { }

pred show{}
run show for 2 State, 1 Graph, 0 Relation


assert a {
	all g1: Graph | all r: Relation | BiSimulacion[g1, g1, r] implies Simulacion[g1, g1, r]
}
check a

assert a2 {
	all g1, g2: Graph | all r: Relation | BiSimulacion[g1, g2, r] implies Simulacion[g1, g2, r]
}
check a2

assert a3 {
	all g1, g2: Graph | all r: Relation | Simulacion[g1, g2, r] implies BiSimulacion[g1, g2, r]
}
check a3


/*

assert b {

}

assert c {

}

*/

