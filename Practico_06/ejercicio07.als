sig Interprete{}

sig Cancion{}

sig Catalogo{
	canciones: set Cancion,
	interpretes: set Interprete,
	interpretaciones: canciones -> interpretes
}{
	//Todas las canciones tienen algun interprete 
	all s: canciones | some i: interpretes | (s -> i) in interpretaciones
	//Todos los interpretes tiene registrada alguna cancion
	all i: interpretes | some s: canciones | (s -> i) in interpretaciones
}


//Devuelve un nuevo catalogo igual al primero pero con esa interpretacion (s->i) agregada
pred Agregar_CancionInterprete[c1, c2: Catalogo, s: Cancion, i: Interprete]{
	// c1 = Catalogo actual
	// c2 = Catalogo nuevo
	// s = Cancion nueva
	// i = interprete de s
	c2.canciones = c1.canciones + s
	c2.interpretes = c1.interpretes + i
	c2.interpretaciones = c1.interpretaciones + (s -> i)
}


//Devuelve un nuevo catalogo igual al primero pero eliminando esa interpretacion (s->i)
pred Eliminar_CancionInterprete[c1, c2: Catalogo, s: Cancion, i: Interprete]{
	// c1 = Catalogo actual
	// c2 = Catalogo nuevo
	// s = Cancion nueva
	// i = interprete de s
	c2.interpretaciones = c1.interpretaciones - (s -> i)
	
	//http://alloy.mit.edu/alloy/documentation/quickguide/a4.html
	//Si esta la misma cancion pero con otro interprete no la borro
	some (/*Poner algo*/) implies c2.canciones = c1.canciones
    // Sino la borro
	else c2.canciones = c1.canciones - s

	//Si esta el mismo interprete pero con otra cancion no lo borro
	some (/*Poner algo*/) implies c2.interpretes = c1.interpretes
    // Sino la borro
	else c2.interpretes = c1.interpretes - i
}

//Devuelve los pares de interpretes que interpretan la misma cancion
fun MismaCancion[c: Catalogo]: Interprete -> Interprete {
//	c.intepretaciones 	c.intepretaciones
}
