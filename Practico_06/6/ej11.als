module practico6/ ej11
//open util/ ordering [Book]
open  practico6/addressBook1h as ABook  // Version abstracta
//open  practico6/addressBook3d as RBook  // Version refinada


/*
sig map{
ad: Addr->Addr' 
nm: Name-> Name' 
}
*/

abstract sig Target { }
sig Addr extends Target { }
abstract sig Name extends Target { }

sig Alias, Group extends this/Name { }

sig Book {
	names: set this/Name,
	addr: names->some Target
} {
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr
}


pred add [b, b': this/Book, n: this/Name, t: Target] {
	t in Addr or some lookup [b, Name&t]
	b'.addr = b.addr + n->t
}

pred del [b, b': this/Book, n: this/Name, t: Target] {
	no b.addr.n or some n.(b.addr) - t
	b'.addr = b.addr - n->t
}

fun lookup [b: this/Book, n: this/Name] : set this/Addr { n.^(b.addr) & this/Addr }


// Defino el mapeo addr abstracto para que vaya de Name en Addr
fun alpha (rB: this/Book): ABook/Book {
	{ aB: ABook/Book | aB.addr =  ^(rB.addr) & (this/Name -> this/Addr) }
}


assert addOK {
	all rB, rB': this/Book, aB, aB': ABook/Book, n: this/Name, a: this/Addr |
		(add[rB, rB', n, a] and aB = alpha[rB] and aB' = alpha[rB'])
		implies
		ABook/add[aB, aB', n, a]
}
check addOK


// Tira contraejemplo! PREGUNTAR! 
assert delOK {
	all rB, rB', aB, aB': Book, n: Name, a: Addr |
		(del[rB, rB', n, a] and aB = alpha[rB] and aB' = alpha[rB'])
		implies
		del[aB, aB', n, a]
}
check delOK

