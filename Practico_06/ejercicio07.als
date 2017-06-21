// Hacer IF - ELSE en Alloy
// http://alloy.mit.edu/alloy/documentation/quickguide/a4.html

sig Interprete{}

sig Cancion{}

sig Catalogo{
	canciones: set Cancion,
	interpretes: set Interprete,
	interpretaciones: canciones -> interpretes
}{
	//Todas las canciones tienen algun interprete 
	//all s: canciones | some i: interpretes | (s->i) in interpretaciones
	canciones = interpretaciones . interpretes
	//Todos los interpretes tiene registrada alguna cancion
	//all i: interpretes | some s: canciones | (s->i) in interpretaciones
	interpretes = canciones . interpretaciones
}

//Devuelve un nuevo catalogo igual al primero pero con esa interpretacion (s->i) agregada
pred Agregar_CancionInterprete[c, c': Catalogo, s: Cancion, i: Interprete]{
	// c = Catalogo actual
	// c' = Catalogo nuevo
	// s = Cancion nueva
	// i = interprete de s
	c'.canciones = c.canciones + s
	c'.interpretes = c.interpretes + i
	c'.interpretaciones = c.interpretaciones + (s->i)
}

run Agregar_CancionInterprete

//Devuelve un nuevo catalogo igual al primero pero eliminando esa interpretacion (s->i)
pred Eliminar_CancionInterprete[c, c': Catalogo, s: Cancion, i: Interprete]{
    // c = Catalogo actual
    // c' = Catalogo nuevo
    // s = Cancion nueva
    // i = interprete de s
    c'.interpretaciones = c.interpretaciones - (s->i)

    //Si esta la misma cancion pero con otro interprete no la borro
    some (s & (c.interpretaciones) . (c.interpretes - i)) implies
        c'.canciones = c.canciones
    // Sino la borro
    else
        c'.canciones = c.canciones - s

    //Si esta el mismo interprete pero con otra cancion no lo borro
    some (i & (c.canciones - s) . (c.interpretaciones)) implies
        c'.interpretes = c.interpretes
    // Sino la borro
    else
        c'.interpretes = c.interpretes - i
}

run Eliminar_CancionInterprete

//Devuelve los pares de interpretes que interpretan la misma cancion
fun MismaCancion[c: Catalogo]: Interprete -> Interprete {
	{ ~(c.interpretaciones) . (c.interpretaciones) }
}

run MismaCancion for 1 but 2 Interprete

pred RunMismaCancion[c: Catalogo]{
	some p: (c.interpretes->c.interpretes) | p = MismaCancion[c]
}

run RunMismaCancion
