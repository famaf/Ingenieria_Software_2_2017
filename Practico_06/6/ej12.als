module practico6/ ej11
open util/ ordering [Book]
 

abstract sig Target { }
sig Addr extends Target { }
abstract sig Name extends Target { }

sig Alias, Group extends Name { }

sig Book {
	names: set Name,
	addr: names->some Target
} {
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr
}


pred add [b, b': Book, n: Name, t: Target] {
	t in Addr or some lookup [b, Name&t]
	b'.addr = b.addr + n->t
}

pred del [b, b': Book, n: Name, t: Target] {
	no b.addr.n or some n.(b.addr) - t
	b'.addr = b.addr - n->t
}

fun lookup [b: Book, n: Name] : set Addr { n.^(b.addr) & Addr }


fact traces {
	no first.addr  // PREGUNTAR! Comienzo con Book vacio ?
	all b: Book - last | let b' = next[b] | some n: Name, t: Target |  // PREGUNTAR! n:b.name O n:Name !!
		add[b, b', n, t] or some lookup[b, n]  // PREGUNTAR! esta bien ejecutar lookup asi?
}


assert addrOK {
	//let b = first | let b' = last | all n: Name, a: Target | n->a in b.addr implies n->a in b'.addr
	all b, b': Book | some n: Name, a: Target | 
		((n->a in b.addr) and (add[b, b', n, a] or some lookup[b,n])) implies
			n->a in b'.addr
}
check addrOK












