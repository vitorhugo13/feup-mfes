open util/ordering[Placement] //4
sig Place {}

sig Network{
	places: set Place,
	connections: places -> places
}{
	connections = ~connections //1
	iden not in connections //1
	all disj p1,p2: places | p1 in p2.*connections //1
}

sig Object{}
sig Placement {
	network : Network,
	objects: set Object,
	-- positions relates objects with places, such that each object has exactly
	-- one place and each place has at most one object
	positions: objects lone -> one Place //2

}{
	-- The places where objects are positioned must belong to the network.
	objects.positions in network.places//2
    
}

-- Moves an object o to an adjacent place p in a placement t,
-- resulting in a new placement t'.
pred moveObject[t: Placement, o: Object, p: Place, t': Placement]{ //3
	-- Pre-conditions:
		-- the object (o) must exist in the initial placement (t)
		o in t.objects
		-- the target place (p) must be unnocupied in the initial placement (t)
		no (t.positions).p
		-- the target place (p) must be adjacent to the initial place of the object (o)
		p in t.network.connections.(o.(t.positions))
		
	-- Post-conditions:
		--(one per field of t’)
		t'.network = t.network
		t'.objects = t.objects
		t'.positions = t.positions ++ o -> p

}

fact Traces {
	all p: Placement - last |let p2 = p.next | some o: Object, pl: Place | moveObject[p,o,pl,p2]
}
run {}