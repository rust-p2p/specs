---- MODULE MCPeer -------------------------------------------------------------
EXTENDS Naturals, Sequences, Bags

CONSTANT Honest, Byzantine, Resource, TrustBound, LoadBound, TrackBound, BufBound, Priority
VARIABLES buf, chan, track, trust
vars == <<buf, chan, track, trust>>

AXIOM Priority \subseteq Nat
Peers == Honest \cup Byzantine
Request == [src : Peers, pr : Priority, res : Resource]
Reply == [res : Resource]
Packet == Request \cup Reply

(* Local == (0 :> {0} @@ 1 :> {1} (\* @@ 2 :> {2} *\)) *)
N == Peers
Value == 0..TrustBound

Neighbour(p1,p2) == TRUE
Peer(p) == INSTANCE Peer WITH P <- p
BufType == [lasthop : Peers, val : Value, res : Resource] \cup [lasthop : Peers, res : Resource]

Init ==
    /\ buf = [p \in Peers |-> EmptyBag]
    /\ track = [p \in Peers |-> EmptyBag]
    /\ trust = [e \in Peers \X Peers |-> 0]
    /\ chan = [e \in Peers \X Peers |-> << >>]

TypeInv ==
    /\ Peer(0)!TypeInv

Next ==
    \/ \E p \in Peers : Peer(p)!Next
    (* \/ *)

(* as long as buf is not empty, exactly one of Rply, Relay and Frwd actions is
   enabled at a time *)
EnableRplyRelayFrwd == []( Peer(0)!EnableRplyRelayFrwd )
ChanSize == \A p1 \in Peers : \A p2 \in Peers : Len(chan[p1,p2]) <= 1
(* these properties should all fail individually during model checking *)
Never == [](
     /\ TRUE
     (* there are paths where buf is nonempty *)
     (* /\ buf[0] = EmptyBag *)
     (* all elements are eventually in the buffer *)
     (* tlc doesn't seem to make any progress checking this property *)
     (* /\ \E e \in [lasthop : Peers, val : Value, res : Resource] \cup [lasthop : Peers, res : Resource] : []( e \notin BagToSet(buf[0]) ) *)
     (* there are paths where track is nonempty *)
     (* /\ track[0] = EmptyBag *)
     (* there are paths that make trust nonzero *)
     (* /\ \A p \in Peers : trust[0,p] = 0 *)
)
--------------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars
================================================================================
