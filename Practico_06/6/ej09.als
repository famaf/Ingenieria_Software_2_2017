module practico6/ ej9
open util/ ordering[State]

fun max[s1, s2: Int]: Int {
	s1 > s2 implies {
		s1
	}
	else {
		s2
	}
}

abstract sig Object { 
	time: Int
}

abstract sig Person { 
	speed: Int
}

one sig FlashLight extends Object {}
one sig IndianaJones, GirlFriend, Father, FatherInLaw extends Person {}


fact speeds {
	IndianaJones.speed = 5
	GirlFriend.speed = 10
	Father.speed = 20
	FatherInLaw.speed = 25
}

fact totalTime {
	FlashLight.time >= 0
}


sig State {
	east: set (Object + Person) ,
	west: set (Object + Person)
}


fact initialState {
	let s0 = first[] | s0.east = (Object + Person) && no s0.west && 
				     FlashLight.time = 60 
}


pred crossBridge[from, from', to, to': (Object + Person)] {
	one x, y: from - FlashLight | 
		from' = from - FlashLight - x - y
		to' = to + FlashLight + x + y
		FlashLight.time - max[x.speed, y.speed]
}






















