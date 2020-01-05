---- MODULE MCPeer -------------------------------------------------------------
EXTENDS Naturals, Sequences, Bags
(* EXTENDS Peer *)
(* Documentation *)
(* VARIABLES buf, chan, track, trust *)
(* vars == <<buf, chan, track, trust>> *)

(* CONSTANT Honest, Byzantine, Resource, TrustBound, LoadBound, TrackBound, Neighbour(_,_), BufBound, Local *)
CONSTANT Honest, Byzantine, Resource, TrustBound, LoadBound, TrackBound, BufBound, (* Local,  *)Priority
VARIABLES buf, chan, track, trust
vars == <<buf, chan, track, trust>>

(* AXIOM Priority \subseteq Nat *)
Peers == Honest \cup Byzantine
Request == [src : Peers, pr : Priority, res : Resource]
Reply == [res : Resource]
Packet == Request \cup Reply

Local == (0 :> {0} @@ 1 :> {1} @@ 2 :> {2})
N == Peers
Value == 0..TrustBound

Neighbour(p1,p2) == TRUE
Peer(p) == INSTANCE Peer WITH P <- p
BufType == [lasthop : Peers, val : Value, res : Resource] \cup [lasthop : Peers, res : Resource]
Init ==
    /\ buf = [p \in Peers |-> EmptyBag]
    /\ track = [p \in Peers |-> EmptyBag]
    /\ trust = [e \in Peers \X Peers |-> TrustBound]
    /\ chan = [e \in Peers \X Peers |-> << >>]

TypeInv ==
    (* /\ TRUE *)
    /\ (* \A p \in Peers :  *)Peer(0)!TypeInv

Next ==
    \E p \in Peers : /\ Peer(p)!Next
                     (* /\ Print(Peer(p)!maxusable,TRUE) *)

EnableRplyRelayFrwd == \A p \in Peers : Peer(p)!EnableRplyRelayFrwd
ChanSize == \A p1 \in Peers : \A p2 \in Peers : Len(chan[p1,p2]) <= 2
--------------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars
================================================================================
