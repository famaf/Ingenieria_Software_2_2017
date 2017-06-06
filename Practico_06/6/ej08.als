module practico6/ riverIQGame
open util/ ordering[State]
// http://dagobah.net/flash/riverIQGame.swf


abstract sig Object {
	manPunch: set Object,
	womanPunch: set Object,
	prisionerPunch: set Object
}

one sig Man, Woman, Police, Prisioner, Boy1, Boy2, Girl1, Girl2 extends Object {}


fact punches {
	manPunch = Man -> Girl1 + Man -> Girl2

	womanPunch = Woman -> Boy1 + Woman -> Boy2

	prisionerPunch =	Prisioner -> Man + Prisioner -> Woman +
			Prisioner -> Boy1 + Prisioner -> Boy2 +
			Prisioner -> Girl1 + Prisioner -> Girl2
}


sig State {
	near: set Object,
	far: set Object
}


fact initialState {
	let s0 = first[] | s0.near = Object and no s0.far 
}


pred crossRiver [from, from', to, to': set Object] {
 	{
		from' = from - Man - Woman
		{
			to' = to - to.manPunch + x + Man or
			to' = to - to.womanPunch + x + Woman 
		}
	}
	or
	{
		{
			from' = from - from.prisionerPunch - Police - Woman
			to' = to + x + Police
		}
		or
		{
			from' = from - Police - Woman
			to' = to - to.womanPunch + x + Woman 
		}
	}
	or
	{
		{
			from' = from - from.prisionerPunch - Police - Man
			to' = to + x + Police
		}
		or
		{
			from' = from - Police - Man
			to' = to - to.manPunch + x + Man 
		}
	}
	or
	one x: from - Man - Woman | {
		from' = from - x - Police
		to' = to - to.prisionerPunch + x + Police
	}
	or
	one x: from - Man - Police | {
		from' = from - from'.manPunch - x - Woman
		to' = to  + x + Police
	}
	or
	one x: from - Woman - Police | {
		from' = from - x - Police
		to' = to - to.prisionerPunch + x + Police
	}
	
}

fact stateTransition {
	all s: State, s': next[s] |
		( Farmer in s.near => crossRiver [ s.near, s'.near, s.far, s'.far ] ) &&
		( Farmer in s.far => crossRiver [ s.far, s'.far, s.near, s'.near ] )
}


pred solvePuzzle[] {
	last[].far = Object 
}


run solvePuzzle for 17 State 




















