open util/ordering[State] 

// El dominio del problema ---------

abstract sig Object { eats: set Object }
 
one sig Farmer, Fox, Chicken, Grain
       extends Object { }

fact eating { eats = Fox -> Chicken + Chicken -> Grain }

// La dinámica --------------------
// Espacio de estado

sig State {
	near: set Object, 
	far: set Object 
	} 

// Estado inicial

fact initialState {
	let s0 = first[] | s0.near = Object && no s0.far 
}

// Transición

pred crossRiver [ from, from', to, to': set Object ] { 
	( from' = from - Farmer && to' = to - to.eats + Farmer) 
	||
	( some item: from - Farmer |
		from' = from - Farmer - item &&
		to' = to - to.eats + Farmer + item
		)
	} 

fact stateTransition {
	all s: State, s': next[s] |
		( Farmer in s.near => crossRiver [ s.near, s'.near, s.far, s'.far ] ) &&
		( Farmer in s.far => crossRiver [ s.far, s'.far, s.near, s'.near ] )
}

// Estado a alcanzar

pred solvePuzzle[] {
	some s: State | s.far = Object 
}

// Ejecución

run solvePuzzle for 11 State 
