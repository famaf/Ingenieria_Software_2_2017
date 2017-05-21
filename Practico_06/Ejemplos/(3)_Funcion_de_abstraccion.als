
// Memoria abstracta

sig Addr, Data { }

sig Memory{
    data: Addr -> lone Data
   }

pred write [ m, m': Memory, a: Addr, d: Data ] {
    m'.data = m.data ++ a -> d
   }

pred read [ m: Memory, a: Addr, d: Data ] {
    let d' = m.data[a] | some d' implies d = d'
}

// Sistema de Memoria Cache

sig Mem { 
    addrs: set Addr,
    map: addrs -> one Data 
   }

sig MainMemory extends Mem { }
sig Cache extends Mem {
    dirty: set addrs
   }

sig CacheSystem {
    cache: Cache,
    main: MainMemory
   }

pred writeMem [m,m': Mem, a: Addr, d: Data ] {
    m'.map = m.map ++ (a -> d)
   }

pred writeSys [s,s': CacheSystem, a: Addr, d: Data ] {
    s'.main = s.main
    writeMem [s.cache,s'.cache,a,d]
    s'.cache.dirty = s.cache.dirty + a
   }

// Función de abstracción

fun alpha [c: CacheSystem]: Memory {
    { m: Memory | m.data = c.main.map ++ c.cache.map }
   }

assert WriteOK {
    all c, c': CacheSystem, 
        a: Addr, d: Data, m, m': Memory |
           ( writeSys[c,c',a,d] and 
             m = alpha[c] and m' = alpha[c'] )
           =>
              write[m,m',a,d] 
   }

check WriteOK
