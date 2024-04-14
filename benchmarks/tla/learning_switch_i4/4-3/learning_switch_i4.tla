---- MODULE learning_switch_i4 ----
\* benchmark: i4-learning-switch

Packet == {"p1","p2","p3"}
Node == {"n1","n2","n3","n4"}

VARIABLE pending
VARIABLE src
VARIABLE dst
VARIABLE link

VARIABLE route_dom
VARIABLE route_tc

vars == <<pending,src,dst,link,route_dom,route_tc>>

NewPacket(p) ==
    /\ pending' = pending \cup {<<p,src[p],src[p]>>}
    /\ UNCHANGED <<src,dst,link,route_dom,route_tc>>

Flood(p,sw0,sw1,sw2) == 
    /\ <<p,sw0,sw1>> \in pending
    /\ <<dst[p],sw1>> \notin route_dom
    /\ LET cond1 == (<<src[p],sw1>> \notin route_dom) /\ (src[p] # sw1)
           cond2 == dst[p] # sw1 IN 
           /\ route_dom' = IF cond1 THEN route_dom \cup {<<src[p],sw1>>} ELSE route_dom
           /\ route_tc' = IF cond1 
                THEN ((route_tc \ ({src[p]} \X Node \X Node)) \cup
                               {<<pa,x,y>> \in ({src[p]} \X Node \X Node) : 
                                    (\/ <<pa,x,y>> \in route_tc 
                                     \/ (<<pa,x,sw1>> \in route_tc /\ <<pa,sw0,y>> \in route_tc))})
                ELSE route_tc
           /\ pending' = IF cond2 
                THEN ((pending \ ({p} \X {sw1} \X Node)) \cup
                            {<<pa,sw1a,y>> \in ({p} \X {sw1} \X Node) : link[sw1a]=y /\ y # sw0})
                ELSE pending
    /\ UNCHANGED <<src,dst,link>>
            
Route(p,sw0,sw1,sw2) ==
    /\ <<p,sw0,sw1>> \in pending
    /\ <<dst[p],sw1>> \in route_dom
    /\ <<dst[p],sw1,sw2>> \in route_tc 
    /\ sw1 # sw2
    /\ \A z \in Node : (<<dst[p],sw1,z>> \in route_tc /\ sw1 # z) => (<<dst[p],sw2,z>> \in route_tc)
    /\ LET cond1 == (<<src[p],sw1>> \notin route_dom) /\ (src[p] # sw1)
           cond2 == dst[p] # sw1 IN 
            /\ route_dom' = IF cond1 THEN route_dom \cup {<<src[p],sw1>>} ELSE route_dom
            /\ route_tc' = IF cond1 
                    THEN ((route_tc \ ({src[p]} \X Node \X Node)) \cup
                                   {<<pa,x,y>> \in ({src[p]} \X Node \X Node) : 
                                        (\/ <<pa,x,y>> \in route_tc 
                                         \/ (<<pa, x, sw1>> \in route_tc /\ <<pa, sw0, y>> \in route_tc))})
                    ELSE route_tc
            /\ pending' = IF cond2 THEN pending \cup {<<p,sw1,sw2>>} ELSE pending
    /\ UNCHANGED <<src,dst,link>>

Next ==
    \/ \E p \in Packet : NewPacket(p)
    \/ \E p \in Packet, sw0,sw1,sw2 \in Node : Flood(p,sw0,sw1,sw2)
    \/ \E p \in Packet, sw0,sw1,sw2 \in Node : Route(p,sw0,sw1,sw2)

Init ==
    /\ route_dom = {}
    /\ route_tc = {<<n,x,y>> \in Node \X Node \X Node : x = y}
    /\ pending = {}
    /\ src \in [Packet -> Node]
    /\ dst \in [Packet -> Node]
    /\ link \in [Node -> Node]
    \* No self-loops in links.
    /\ \A x \in Node : link[x] # x
    \* Symmetric links.
    /\ \A x,y \in Node : (link[x] = y) => (link[y] = x)

Spec == Init /\ [][Next]_vars

Safety ==
    \A n,x,y,z \in Node : 
        /\ <<n,x,x>> \in route_tc
        /\ (<<n,x,y>> \in route_tc /\ <<n,y,z>> \in route_tc) => <<n,x,z>> \in route_tc
        /\ (<<n,x,y>> \in route_tc /\ <<n,y,x>> \in route_tc) => (x = y)
        /\ <<n,x,y>> \in route_tc /\ <<n,x,z>> \in route_tc => (<<n,y,z>> \in route_tc \/ <<n,z,y>> \in route_tc)

TypeOK ==
    /\ route_dom \in SUBSET (Node \X Node)
    /\ route_tc \in SUBSET (Node \X Node \X Node)
    /\ pending \in SUBSET (Packet \X Node \X Node)
    /\ src \in [Packet -> Node]
    /\ dst \in [Packet -> Node]
    /\ link \in [Node -> Node]

====
