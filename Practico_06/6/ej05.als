module practico6/ binaryRelation


sig Elem {}

sig BinaryRel {
	rel: Elem -> Elem
}
 

pred Reflex[r: BinaryRel] {
	//all e1: Elem | e1 in e1.(r.rel)
	(iden & Elem->Elem) in r.rel
}

pred AntiSim[r: BinaryRel] {
	//all e1, e2: Elem | (e1->e2 in r.rel and  e2->e1 in r.rel) implies (e1 = e2)
	r.rel & ~(r.rel) in iden
}

pred Trans[r: BinaryRel] {
	//all e1, e2, e3: Elem | (e1->e2 in r.rel and e2->e3 in r.rel) implies (e1->e3  in r.rel)
	(r.rel).(r.rel) in r.rel
}

pred PreOrder[r: BinaryRel] {
	Reflex[r]
	Trans[r]
}
run PreOrder for 3 but 1 BinaryRel

pred PartialOrder[r: BinaryRel] {
	PreOrder[r]
	AntiSim[r]
}
run PartialOrder for 3 but 1 BinaryRel

pred TotalOrder[r: BinaryRel] {
	PartialOrder[r]
	//all e1, e2: Elem | (e1->e2 in r.rel) or (e2->e1 in r.rel)
	((Elem -> Elem - r.rel).(Elem -> Elem - r.rel)) & (iden&(Elem->Elem)) = none->none  // TAREA: ACORTAR!
}

pred StrictOrder[r: BinaryRel] {
	Trans[r]
	((Elem -> Elem - r.rel).(Elem -> Elem - r.rel)) & (iden&(Elem->Elem)) = none->none
	//all e1, e2: r.elem | e1->e2 in r.rel iff e1->e2 in r.rel and e1 != e2
	r.rel & ~(r.rel) = none->none
}

pred First[r: BinaryRel] {
	one e1: Elem | all e2: Elem-e1 | (e1->e2 in r.rel) and (not e2->e1 in r.rel)
}

pred Last[r: BinaryRel] {
	one e2: Elem | all e1: Elem-e2 | (not e1=e2) and (e1->e2 in r.rel) and (not e2->e1 in r.rel)
}

assert a {
	all r: BinaryRel | PartialOrder[r] implies TotalOrder[r]
}
check a for 5 but 2 BinaryRel

assert b {
	all r: BinaryRel | PartialOrder[r] implies First[r]
}
check b for 5 but 2 BinaryRel

assert c { }
check c for 5 but 2 BinaryRel

assert d {
	all r1, r2: BinaryRel | (StrictOrder[r1] and StrictOrder[r2]) implies StrictOrder[r1+r2]
}
check d for 5 but 2 BinaryRel

assert e { }
check e for 5 but 2 BinaryRel

