
// Dominio

abstract sig List {}

sig Element {}

one sig EmptyList extends List {}

sig NonEmptyList extends List {
    element: Element,
    rest: List
   }

// Axioma de generación generando infinitas listas

fact ListGenerator {
    all l: List, e: Element |
        some l': List | l'.rest = l  and  l'.element = e
   }

// Aserción obviamente no válida que da verdadera

assert ObviouslyNotValid { all l: List | all l': List | l'.rest = l or l = l' }

check ObviouslyNotValid

// Predicado auxiliar

pred show [] {}

// Genera sólo una instancia (la lista vacía)

run show

// No genera ninguna instancia

run show for 3 but exactly 1 Element
