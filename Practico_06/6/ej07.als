module practico6/ musicCatalog


sig Interprete {}

sig Cancion {}

sig Catalogo {
	canciones: set Cancion,
	interpretes: set Interprete,
	interpretaciones: canciones -> interpretes
}{
	//all s: canciones | some i: interpretes | (s -> i) in interpretaciones
	//all i: interpretes | some s: canciones | (s -> i) in interpretaciones
	interpretaciones.interpretes = canciones  // Todas las canciones tienen interprete
	canciones.interpretaciones = interpretes  // Todas los interpretes tienen cancion
}


pred add[c, c': Catalogo, s: Cancion, i: Interprete] {
	c'.canciones = c.canciones + s
	c'.interpretes = c.interpretes + i
	c'.interpretaciones = c.interpretaciones + (s -> i)
}

pred del[c, c': Catalogo, s: Cancion, i: Interprete] {
	// Borro la interpretacion
	c'.interpretaciones = c.interpretaciones - s->i
	
	// Podria ser asi?
	/*
	c'.canciones = c.canciones - s
	c'.interpretes = c.interpretes - i
	*/
	
	// Si tengo la misma cancion con otro interprete la dejo, sino la borro
	some (s & (c.interpretaciones).(c.interpretes - i)) implies
		c'.canciones = c.canciones
	else
		c'.canciones = c.canciones - s

	// Si tengo el mismo interprete con otra cancion lo dejo, sino lo borro
	some (i & (c.canciones - s).(c.interpretaciones)) implies
		c'.interpretes = c.interpretes
	else
		c'.interpretes = c.interpretes - i
}

fun par[c: Catalogo]: Interprete -> Interprete {
	(~(c.interpretaciones)).(c.interpretaciones)
}


pred consistent [c:Catalogo] {
	all s: c.canciones | some i: c.interpretes | (s->i) in c.interpretaciones
	all i: c.interpretes | some s: c.canciones | (s->i) in c.interpretaciones
}


assert a1 { 
	all c, c': Catalogo, i: Interprete, s: Cancion |
		(consistent[c] and del[c, c', s, i]) implies consistent[c']
}
check a1 for 10

assert a2 { 
	all c, c': Catalogo, i: Interprete, s: Cancion |
		(consistent[c] and add[c, c', s, i]) implies consistent[c']
}
check a2





