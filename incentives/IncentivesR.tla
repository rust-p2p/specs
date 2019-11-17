---- MODULE IncentivesR -----------------------------------------------------
EXTENDS Naturals, Sequences, Bags
(* Documentation *)
(* This specification deals with the handling of packets according to the incentive scheme *)

(* Implicit assumptions include reliable transport layer WITH no delay, the neighbour
a request is forwarded to is irrelevant, no peer can be impersonated (sources are cryptographically signed),
load is modelled as binary, fixed number of peers guaranteed to be honest *)
--------------------------------------------------------------------------------
(* CONSTANT Peers *)
VARIABLES trust, relaytable, q_in, q_out
vars == <<trust, relaytable, q_in, q_out>>

(* For the moment these are fixed *)
Peers == 0..1
Resources == 0..0
Priority == 0..1
MaxTrust == 2
LoadBound == 2
OutBound == 1
Packet == [src : Peers, dst : Peers, type : {0,1}, p : Priority, res : Resources]

Min(x, y) == IF x >= y THEN y ELSE x
(* Min(x) == x *)
Max(x, y) == IF x >= y THEN x ELSE y
EffPriority(p,paket) == Min(paket.p, trust[p,paket.src])
Debit(p,paket) == [trust EXCEPT ![p,paket.p] = Min(@ - paket.p, 0) ]
Credit(p,paket) == [trust EXCEPT ![p,paket.p] = Max(@ + paket.p, MaxTrust) ]

TypeInv ==
    /\ trust \in [Peers \X Peers -> 0..MaxTrust+1]
    /\ \A p1 \in Peers : \A p2 \in Peers : p2 # p1 => trust[p1,p2] \in 0..MaxTrust
    /\ \A peer \in Peers : trust[peer,peer] = MaxTrust + 1
    /\ relaytable \in [Peers -> Seq(Packet)]
    /\ q_in \in [Peers -> Seq(Packet)]
    /\ q_out \in [Peers -> Seq(Packet)]

--------------------------------------------------------------------------------

Init ==
    /\ TypeInv
    /\ relaytable = [peer \in Peers |-> << >>]
    /\ q_in = [peer \in Peers |-> << >>]
    /\ q_out = [peer \in Peers |-> << >>]
    /\ \A p1 \in Peers : \A p2 \in Peers : p2 # p1 => trust[p1,p2] = 0
    /\ \A peer \in Peers : trust[peer,peer] = MaxTrust + 1

Send(p,pkt) ==
    /\ q_out[p] # << >>
    /\ pkt = Head(q_out[p])
    /\ q_out' = [q_out EXCEPT ![p] = Tail(q_out[p])]
    /\ UNCHANGED <<trust, relaytable>>

Rcv(p,pkt) ==
    /\ \/ /\ Len(q_in[p]) < LoadBound
          /\ q_in' = [q_in EXCEPT ![p] = Append(q_in[p],pkt)]
       \/ /\ Len(q_in[p]) = LoadBound
          /\ q_in' = [q_in EXCEPT ![p] = Append(q_in[p], [pkt EXCEPT !.p = EffPriority(p,pkt)])]
    /\ UNCHANGED <<trust, relaytable>>


Next == \E p1 \in Peers :
        \E p2 \in Peers \ {p1} :
        \E pkt \in Packet : /\ Send(p1,pkt)
                            /\ Rcv(p2,pkt)

Spec == Init /\ [][Next]_vars
================================================================================
THEOREM Spec => []TypeInv
================================================================================
