module practico6/ memorySystem


sig Addr, Data {}

sig Memory {
	addrs: set Addr,
	map: addrs -> one Data
}

sig MainMemory extends Memory { }

sig Cache extends Memory {
	dirty: set addrs
}

sig System {
	cache: Cache,
	main: MainMemory
}


// Write
pred Write[s, s': System, d: Data, a: Addr] {
	s'.cache.map = s.cache.map ++ (a -> d)
	s'.cache.addrs = s.cache.addrs+ a
	s'.cache.dirty = s.cache.dirty + a
	s'.main = s.main
}

// Flush
pred Flush[s, s': System] {
	s'.main.map = s.main.map ++ s.cache.map
	s'.cache.map = s.cache.map
	s'.cache.addrs = s.cache.addrs
	s'.cache.dirty = none
}

// Load
pred Load[s, s': System, a: Addr] {
	s'.cache.addrs = s.cache.addrs + a
	s'.cache.map = s.cache.map ++ (a->s.main.map[a])
	s'.cache.dirty = s.cache.dirty + a
	s'.main.map = s.main.map
}

// Read
pred Read[s, s': System, d: Data, a: Addr] {
	(not (a in s.cache.addrs)) implies
		Load[s, s', a]
	else {
		s'.main = s.main
		s'.cache = s.cache
		d = s'.cache.map[a]
	}
}


// Predicado de consistencia
pred Consistent[s: System] {
    (s.cache.map - (s.cache.dirty->Data)) in s.main.map
}


// Asserts
assert WriteInv {
	all s, s': System, a: Addr, d: Data |
		(Consistent [s] and Write [s, s', d, a] => Consistent [s'])
}
check WriteInv

assert FlushInv {
	all s, s': System |
		(Consistent [s] and Flush [s, s'] => Consistent [s'])
}
check FlushInv

assert LoadInv {
	all s, s': System, a: Addr |
		(Consistent [s] and Load [s, s', a] => Consistent [s'])
}
check LoadInv

assert ReadInv {
	all s, s': System, a: Addr, d: Data |
		(Consistent [s] and Read [s, s', d, a] => Consistent [s'])
}
check ReadInv

