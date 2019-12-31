---- MODULE MCPeer -------------------------------------------------------------
EXTENDS Naturals, Sequences, Bags
(* EXTENDS Peer *)
(* Documentation *)
(* VARIABLES buf, chan, track, trust *)
(* vars == <<buf, chan, track, trust>> *)

(* CONSTANT Honest, Byzantine, Resource, TrustBound, LoadBound, TrackBound, Neighbour(_,_), BufBound, Local *)
CONSTANT Honest, Byzantine, Resource, TrustBound, LoadBound, TrackBound, BufBound, Local
VARIABLES buf, chan, track, trust
vars == <<buf, chan, track, trust>>

Priority == 0..TrustBound
Peers == Honest \cup Byzantine
Request == [src : Peers, pr : Priority, res : Resource]
Reply == [res : Resource]
Packet == Request \cup Reply

N == Peers
Value == 0..TrustBound

Neighbour(p1,p2) == TRUE
Peer(p) == INSTANCE Peer WITH P <- p, buf <- buf[p], chan <- chan, track <- track[p], trust <- trust[p], Priority <- Priority
BufType == [lasthop : Peers, val : Value, res : Resource] \cup [lasthop : Peers, res : Resource]
Init ==
    /\ buf = [e \in Peers \X BufType |-> EmptyBag]
    (* /\ \A p \in Peers : buf[p] = EmptyBag *)
    /\ track = [p \in Peers |-> EmptyBag]
    (* /\ trust = [n \in N \ {P} |-> 0] *)
    (* /\ \A p \in Peers : Peer(p)!Init *)
    /\ chan = [e \in Peers \X Peers |-> << >>]
    /\ trust = [e \in Peers \X Peers |-> 0]
    (* /\ \A e \in Peers \X Peers : trust[e[1],e[2]] = 0 *)

TypeInv ==
    (* /\ \A p \in Peers : Peer(p)!TypeInv *)
    /\ chan \in [Peers \X Peers -> Seq(Packet)]
    /\ \A P \in Peers : \A p \in Peers : P # p => trust[P,p] \in 0..TrustBound
    /\ \A p \in Peers : IsABag(track[p])
    /\ \A p \in Peers : \A e \in BagToSet(track[p]) : e \in [nxthop : N, lasthop : N, val : Value, res : Resource]
    /\ \A p \in Peers : IsABag(buf[p])
    /\ \A p \in Peers : \A e \in BagToSet(buf[p]) : e \in [lasthop : Peers, val : Value, res : Resource]
                                                     \cup [lasthop : Peers, res : Resource]

Next ==
    \E p \in Peers : /\ Peer(p)!Next
                     /\ UNCHANGED vars
--------------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars
================================================================================
