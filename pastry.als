open util/ordering[Id] as I
open util/ordering[Time] as T

sig Time {} // Assinatura relacionada com o tempo

one sig Network {
	connected : Node set -> set Time // Esta relação indica quais os Nodos conectados, num momento
}

abstract sig Id {
	succ: one Id, // Sucessor de um certo Id no anel
	ant: one Id // Antecessor de um certo Id no anel
}

sig Key extends Id {} // Chave, pode ser guardas em hashtables

sig Node extends Id {
	hashtable: Key set -> set Time,
	neighboursHT: Key set -> set Time, // Chaves guardadas pelos vizinhos
	lset: Node set -> set Time, // Vizinhos à esquerda
	rset: Node set -> set Time // Vizinhos à direita
}

one sig First in Id {} // Primeiro Id no anel
one sig Last in Id {} // Ultimo Id no anel

/* Forçar formato em anel */
fact RingShape {
	// Igualar o First e o Last da ordem total à ordem do anel
	First = first
	Last = last

	// O First é vizinho do Last e vice-versa
	First.ant = Last
	Last.succ = First

	// Não existe circularidade entre o First e o Last no anel
	all i:Id-Last | i.succ = i.next
	all i:Id-First | i.ant = i.prev

}

/* Funções para auxiliar o tema */
fun Connected[t:Time,n:Node]: set Node {
	{n:Node | n in Network.connected.t }
}

/* INVARIANTES */

// Chaves armazenadas por um determinado Nodo encontram-se
// na área de cobertura desse nodo
pred inv1[t:Time] {
	all n:Network.connected.t,k:Key {
		k in n.hashtable.t and gt[k,n] => no n':Network.connected.t | n' in (n.^next & k.^prev)
	}
	all n:Network.connected.t,k:Key {
		k in n.hashtable.t and lt[k,n] => no n':Network.connected.t | n' in (n.^prev & k.^next)
	}
}

// Cada chave é coberta apenas por um nodo conectado
pred inv2[t:Time] {
	all k:Key | lone (hashtable.t).k
	all k:Key | one (hashtable.t).k => (hashtable.t).k in Network.connected.t
}

// Cada nodo conectado guarda as chaves dos vizinhos
pred inv3[t:Time] {
	all n:Network.connected.t | n.neighboursHT.t = (n.lset.t + n.rset.t).hashtable.t
}


// Os lset's e rset's são constituidos por apenas nodos conectados
pred inv4[t:Time] {
	((Network.connected.t).rset.t + (Network.connected.t).lset.t) in Network.connected.t
}

// Qualquer dois nodos se o primeiro é vizinho do segundo, então o segundo é vizinho do primeiro
pred inv5[t:Time] {
	all n1,n2:Network.connected.t | n1 in n2.lset.t => n2 in n1.rset.t
	all n1,n2:Network.connected.t | n1 in n2.rset.t => n2 in n1.lset.t
}

// O lset e o rset de um Nodo tem um 
// conjunto dos menores nodos conectados consecutivos
pred inv6[t:Time] {

	/* Caso geral */
	all n:Network.connected.t-First | some n.lset.t => n.lset.t in n.^ant
	all n1:Network.connected.t-First,n2:Network.connected.t | n2 in n1.lset.t => ! some n3:Network.connected.t { 
		n3 in (n1.^prev & n2.^next) and n3 not in n1.lset.t
	}

	all n:Network.connected.t-Last | some n.rset.t => n.rset.t in n.^succ
	all n1:Network.connected.t-Last,n2:Network.connected.t | n2 in n1.rset.t => ! some n3:Network.connected.t { 
		n3 in (n1.^next & n2.^prev) and n3 not in n1.rset.t
	}

	/* Caso para o First e Last */
	all n:First | n in Network.connected.t => n.lset.t in Last.*prev
	all n:Last | n in Network.connected.t => n.rset.t in First.*next

	all n1:First,n2:Network.connected.t | n1 in Network.connected.t and n2 in n1.lset.t => ! some n3:Network.connected.t {
		n3 in n2.^next and n3 not in n1.lset.t
	}

	all n1:Last,n2:Network.connected.t | n1 in Network.connected.t and n2 in n1.rset.t => ! some n3:Network.connected.t {
		n3 in n2.^prev and n3 not in n1.rset.t
	}

}

// Todos os nodos conectados possuem no minimo um Nodo no seu lset e rset
// quando existem pelo menos dois nodos conectados na rede
pred inv7[t:Time] {
	! lone Network.connected.t => all n:Network.connected.t | some n.lset.t
	! lone Network.connected.t => all n:Network.connected.t | some n.rset.t
}

// Um nodo não se encontra no seu lset nem rset
pred inv8[t:Time] {
	all n:Network.connected.t | n not in n.lset.t
	all n:Network.connected.t | n not in n.rset.t
}

pred invs[t:Time] {
	inv1[t]
	inv2[t]
	inv3[t]
	inv4[t]
	inv5[t]
	inv6[t]
	inv7[t]
	inv8[t]
}

/* Funções auxiliares */

fun minInRing[t:Time]: lone Node {
	min[Network.connected.t]
}

fun maxInRing[t:Time]: lone Node {
	max[Network.connected.t]
}

fun nextNodeInRing[t:Time,n:Node]: lone Node {
	min[{ n1:Network.connected.t-n | gt[n1,n] }]
}

fun prevNodeInRing[t:Time,n:Node]: lone Node {
	max[{ n1:Network.connected.t-n | lt[n1,n] }]
}

/* Operações */

/***** ESTADO INICIAL *****/

pred init[t:Time] {
	no Network.connected.t
	no hashtable.t
	no rset.t
	no lset.t
	no neighboursHT.t
}

check initIsValid {
	all t:Time | init[t] => invs[t]
} for 5

/***** JOIN *****/
pred join[t1,t2:Time,n:Node] {
	// Pré-condições
	n not in Network.connected.t1
	no n.hashtable.t1
	no n.neighboursHT.t1
	no n.rset.t1
	no n.lset.t1
	
	// Pós-condições
	Network.connected.t2 = Network.connected.t1 + n

	/* Acordar lset e rsets */
	(#Network.connected.t1 >= 1) and lt[n,minInRing[t1]] =>
		lset.t2 = lset.t1 + n->maxInRing[t1] + nextNodeInRing[t1,n]->n
		rset.t2 = rset.t1 + n->nextNodeInRing[t1,n] + maxInRing[t1]->n

	(#Network.connected.t1 >= 1) and gt[n,maxInRing[t1]] =>
		lset.t2 = lset.t1 + n->prevNodeInRing[t1,n] + minInRing[t1]->n
		rset.t2 = rset.t1 + n->minInRing[t1] + prevNodeInRing[t1,n]->n

	(#Network.connected.t1 >= 1) and ! gt[n,maxInRing[t1]] and !lt[n,minInRing[t1]] =>
		lset.t2 = lset.t1 + n->prevNodeInRing[t1,n] + nextNodeInRing[t1,n]->n
		rset.t2 = rset.t1 + n->nextNodeInRing[t1,n] + prevNodeInRing[t1,n]->n

	// O nodo sabe quais as chaves dos vizinhos
	(! lone Network.connected.t2) => neighboursHT.t2 = neighboursHT.t1 + n->(n.lset.t2 + n.rset.t2).hashtable.t2

	// Frame conditions
	hashtable.t2 = hashtable.t1

	/* Network ainda é pequena (<2 Nodos) */
	lone Network.connected.t2 => lset.t2 = lset.t1
	lone Network.connected.t2 => rset.t2 = rset.t1
	lone Network.connected.t2 => neighboursHT.t2 = neighboursHT.t1

}

run joinIsConsistent {
	some t:Time,n:Node | join[t,t.next,n]
} for 5

check joinIsValid {
	all t:Time | init[t] => invs[t]
	all t:Time-T/last,n:Node | invs[t] and join[t,t.next,n] => invs[t.next]
} for 5


/***** DISJOIN *****/
/*

Não é preservado o invariante 7 e, devido a falta de tempo não conseguimos
corrigir.

pred disjoin[t1,t2:Time,n:Node] {
	// Pré-condições
	n in Network.connected.t1
	
	// Pós-condições
	Network.connected.t2 = Network.connected.t1 - n
	
	// Vizinhos também removem nodo
	rset.t2 = ((rset.t1 - ((rset.t1).n)->n) + (n.lset.t1)->(n.rset.t1)) - (iden & (Node->Node)) - n->(n.rset.t1)
	lset.t2 = ((lset.t1 - ((lset.t1).n)->n) + (n.rset.t1)->(n.lset.t1)) - (iden & (Node->Node)) - n->(n.rset.t1)
	
	// Os vizinhos ficam com as chaves do nodo
	n != minInRing[t1] => hashtable.t2 = ((hashtable.t1 - n->Key) + prevNodeInRing[t1,n]->(n.hashtable.t1))
	n != minInRing[t1] => neighboursHT.t2 = neighboursHT.t1 + 
					  prevNodeInRing[t1,n]->(prevNodeInRing[t1,n].lset.t2 + prevNodeInRing[t1,n].rset.t2).hashtable.t2 +
					  nextNodeInRing[t1,n]->(nextNodeInRing[t1,n].lset.t2 + nextNodeInRing[t1,n].rset.t2).hashtable.t2 + 
					  (prevNodeInRing[t1,n].lset.t2 + prevNodeInRing[t1,n].rset.t2)->prevNodeInRing[t1,n].hashtable.t2 -
					  prevNodeInRing[t1,n]->(n.hashtable.t1)
	n = minInRing[t1] => hashtable.t2 = ((hashtable.t1 - n->Key) + nextNodeInRing[t1,n]->(n.hashtable.t1))
	n = minInRing[t1] => neighboursHT.t2 = neighboursHT.t1 + 
					  nextNodeInRing[t1,n]->(nextNodeInRing[t1,n].lset.t2 + nextNodeInRing[t1,n].rset.t2).hashtable.t2 +
					  nextNodeInRing[t1,n]->(nextNodeInRing[t1,n].lset.t2 + nextNodeInRing[t1,n].rset.t2).hashtable.t2 + 
					  (nextNodeInRing[t1,n].lset.t2 + nextNodeInRing[t1,n].rset.t2)->nextNodeInRing[t1,n].hashtable.t2 -
					  nextNodeInRing[t1,n]->(n.hashtable.t1)

	// Frame conditions
}

run disjoinIsConsistent {
	some t:Time,n:Node | disjoin[t,t.next,n]
} for 5

check disjoinIsValid {
	all t:Time | init[t] => invs[t]
	all t:Time-T/last,n:Node | invs[t] and disjoin[t,t.next,n] => invs[t.next]
} for 5
*/

/***** PUT KEY *****/
pred putKey[t1,t2:Time,k:Key,n:Node]{
    --Pré-condições
    n in Network.connected.t1
    k not in (Network.connected.t1).hashtable.t1
    gt[k,n] => no n':Network.connected.t1 | n' in (n.^next & k.^prev)
    lt[k,n] => no n':Network.connected.t1 | n' in (n.^prev & k.^next)
    
    --Pós-condições
    hashtable.t2 = hashtable.t1 + n->k
    neighboursHT.t2 = neighboursHT.t1 + (n.lset.t1+ n.rset.t1)->k + ((lset.t1+rset.t1).n)->k

    --Frame conditions
    Network.connected.t2 = Network.connected.t1
    lset.t2 = lset.t1
    rset.t2 = rset.t1
}

run putKeyIsConsistent {
    some t:Time,k:Key,n:Node | putKey[t,t.next,k,n]
} for 5

check putKeyIsValid {
	all t:Time | init[t] => invs[t]
    all t:Time-T/last,k:Key,n:Node | invs[t] and putKey[t,t.next,k,n] => invs[t.next]
} for 5

/*** DELETE KEY ***/
pred deleteKey[t1,t2:Time,k:Key]{
    --Pré-condições
    k  in (Network.connected.t1).hashtable.t1
    
    --Pós-condições
    hashtable.t2 = hashtable.t1 - Node->k
    neighboursHT.t2 = neighboursHT.t1 - ((Network.connected.t1).lset.t1 + (Network.connected.t1).rset.t1)->k 
					  - ((lset.t1+rset.t1).(Network.connected.t1))->k

    --Frame conditions
    Network.connected.t2 = Network.connected.t1
    lset.t2 = lset.t1
    rset.t2 = rset.t1
}

run deleteKeyIsConsistent {
    some t:Time,k:Key | deleteKey[t,t.next,k]
} for 5

check deleteKeyIsValid {
	all t:Time | init[t] => invs[t]
    all t:Time-T/last,k:Key | invs[t] and deleteKey[t,t.next,k] => invs[t.next]
} for 5

/*** PROPRIEDADES ***/

/* Descomentar para verificar as propriedades */

/*** TRACE IDIOM ***/
/*
fact Trace {
	init[T/first]
	all t:Time-T/last | some n:Node,k:Key | join[t,t.next,n] or putKey[t,t.next,k,n] or deleteKey[t,t.next,k]
}

check TraceIsValid {
	all t:Time | invs[t]
}

// Eventualmente todos os nodos vão estar conectados
assert AllJoin {
	no t:Time | Network.connected.t = Node
}

// Eventualmente vão existir nodos conectados
assert NeverJoin {
	no t:Time | some Network.connected.t
}

check AllJoin for 5 but exactly 2 Node
check NeverJoin for 5 but exactly 2 Node

*/

