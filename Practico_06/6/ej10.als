module practico6/ HanoiTowers
open util/ ordering[State]


abstract sig Disk { order: set Disk }

// Disk1 > Disk2 > Disk3 > Disk4
one sig Disk1, Disk2, Disk3, Disk4 
	extends Disk { }


fact orders {
	order =  Disk1 -> Disk2 + Disk1 -> Disk3 + Disk1 -> Disk4 +
			Disk2 -> Disk3 + Disk2 -> Disk4 +
			Disk3 -> Disk4
}


sig State {
	left: set Disk,
	center: set Disk,
	right: set Disk
}


fact initialState {
	let s0 = first[] | (s0.left = Disk) and (no s0.center) and (no s0.right)
}


fact correctMove {
	all s: State
	(Disk = from) implies (from' = from - Disk4 and to' = to - to.order + Disk4)
	((Disk1 + Disk2 + Disk3) = from) implies (from' = from - Disk3 and to' = to - to.order + Disk3)
	((Disk1 + Disk2) = from) implies (from' = from - Disk2 and to' = to - to.order + Disk2)
	((Disk1 + Disk3) = from) implies (from' = from - Disk3 and to' = to - to.order + Disk3)
	((Disk1 + Disk4) = from) implies (from' = from - Disk4 and to' = to - to.order + Disk4)
	((Disk2 + Disk3) = from) implies (from' = from - Disk3 and to' = to - to.order + Disk3)
	((Disk2 + Disk4) = from) implies (from' = from - Disk4 and to' = to - to.order + Disk4)
	((Disk3 + Disk4) = from) implies (from' = from - Disk4 and to' = to - to.order + Disk4)
	((Disk1) = from) implies (from' = from - Disk1 and to' = to - to.order + Disk1)
	((Disk2) = from) implies (from' = from - Disk2 and to' = to - to.order + Disk2)
	((Disk3) = from) implies (from' = from - Disk3 and to' = to - to.order + Disk3)
	((Disk4) = from) implies (from' = from - Disk4 and to' = to - to.order + Disk4)
}


fact stateTransition {
	all s: State, s': next[s] |
		moveDisk[s.left, s'.left, s.center, s'.center] or
		moveDisk[s.left, s'.left, s.right, s'.right] or
		moveDisk[s.center, s'.center, s.left, s'.left] or
		moveDisk[s.center, s'.center, s.right, s'.right] or
		moveDisk[s.right, s'.right, s.left, s'.left] or
		moveDisk[s.right, s'.right, s.center, s'.center]
}


pred solvePuzzle[] {
	last[].right = Disk
}
run solvePuzzle for 15 State 















