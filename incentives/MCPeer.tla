---- MODULE MCPeer -------------------------------------------------------------
EXTENDS Naturals, Sequences, Bags, TLCExt

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
Chng(var,e,to) == [var EXCEPT ![e] = to]
buf0 == [p \in Peers |-> EmptyBag]
track0 == [p \in Peers |-> EmptyBag]
trust0 == [e \in Peers \X Peers |-> TrustBound]
chan0 == [e \in Peers \X Peers |-> << >>]

RECURSIVE Change(_,_)
Change(f,e) ==
    IF e = << >> THEN f
    ELSE [Change(f,Tail(e)) EXCEPT ![e[1,1]] = e[1,2]]


Init ==
    (* \/ /\ buf = buf0 *)
    (*    /\ track = track0 *)
    (*    /\ trust = trust0 *)
    (*    /\ chan = chan0 *)
    (* different initial conditions for more complete coverage report *)
    (* the following initial conditions should cover all branches of the Rcv action *)
    (* 2nd initial condition *)
    \/ /\ trust = Chng(trust0,<<0,1>>,TrustBound)
       /\ buf = Chng(buf0,2,([res |-> 1, lasthop |-> 1] :> 1))
       /\ chan = Chng(chan0,<<1,0>>,<<[src |-> 1, pr |-> 0, res |-> 0]>>)
       /\ track = track0
    (* 2nd initial condition *)
    \/ /\ trust = Chng(Chng(trust0,<<0,1>>,1),
                                   <<0,2>>,1)
       /\ buf = Chng(buf0,2,([res |-> 1, lasthop |-> 1] :> 1))
       /\ chan = Chng(chan0,<<2,1>>,<<[src |-> 2, pr |-> 0, res |-> 0]>>)
       /\ track = Chng(Chng(track0,0,([res |-> 1, lasthop |-> 2, val |-> 0, nxthop |-> 0] :> 1)),
                                   2,( [res |-> 0, lasthop |-> 1, val |-> 0, nxthop |-> 2] :> 1 @@
                                       [res |-> 1, lasthop |-> 1, val |-> 0, nxthop |-> 0] :> 1 ))
    (* 3nd initial condition *)
    \/ /\ trust = trust0
       /\ buf = Chng(buf0,0,([res |-> 0, lasthop |-> 1] :> 1))
       /\ chan = chan0
       /\ track = Chng(Chng(track0,0,( [res |-> 1, lasthop |-> 2, val |-> 0, nxthop |-> 0] :> 1 @@
                                       [res |-> 1, lasthop |-> 1, val |-> 1, nxthop |-> 2] :> 1 )),
                                   2,( [res |-> 0, lasthop |-> 1, val |-> 0, nxthop |-> 2] :> 1 @@
                                       [res |-> 1, lasthop |-> 1, val |-> 0, nxthop |-> 0] :> 1 ))
    (* 4nd initial condition *)
    \/ /\ trust = trust0
       /\ buf = Chng(buf0,0,([res |-> 0, lasthop |-> 1, val |-> 0] :> 1))
       (* /\ buf = (0 :> ([res |-> 0, lasthop |-> 1, val |-> 0] :> 1) @@ 1 :> <<>> @@ 2 :> <<>>) *)
       /\ chan = chan0
       /\ track = track0
    (* 5nd initial condition *)
    \/ /\ trust = trust0
       /\ buf = Chng(buf0,0,([res |-> 0, lasthop |-> 2, val |-> 0] :> 1 @@ [res |-> 1, lasthop |-> 0, val |-> 0] :> 1))
       (* /\ buf = (0 :> ([res |-> 0, lasthop |-> 0, val |-> 0] :> 1 @@ [res |-> 1, lasthop |-> 0, val |-> 0] :> 1) @@ 1 :> <<>> @@ 2 :> <<>>) *)
       /\ chan = chan0
       /\ track = track0
    (* 6th initial condition *)
    \/ /\ trust = Chng(Chng(trust0,<<0,1>>,2),
                                   <<0,2>>,2)
       /\ buf = Chng(buf0,0,([res |-> 0, lasthop |-> 1] :> 1 @@
                             [res |-> 2, lasthop |-> 1] :> 1 @@
                             [res |-> 2, lasthop |-> 1] :> 1 @@
                             [res |-> 2, lasthop |-> 1] :> 1 @@
                             [res |-> 2, lasthop |-> 1] :> 1 @@
                             [res |-> 2, lasthop |-> 1] :> 1 @@
                             [res |-> 2, lasthop |-> 1] :> 1 @@
                             [res |-> 2, lasthop |-> 1] :> 1 @@
                             [res |-> 2, lasthop |-> 0, val |-> 1] :> 1 @@
                             [res |-> 0, lasthop |-> 1, val |-> 0] :> 1 @@
                             [res |-> 0, lasthop |-> 3, val |-> 1] :> 1 @@
                             [res |-> 0, lasthop |-> 1, val |-> 0] :> 1 @@
                             [res |-> 1, lasthop |-> 1, val |-> 0] :> 1 ))
       /\ chan = chan0
       /\ track = Chng(Chng(track0,0,( [res |-> 1, lasthop |-> 2, val |-> 0, nxthop |-> 0] :> 1 @@
                                       [res |-> 1, lasthop |-> 1, val |-> 1, nxthop |-> 2] :> 1 @@
                                       [res |-> 2, lasthop |-> 1, val |-> 1, nxthop |-> 1] :> 1 )),
                                   2,( [res |-> 0, lasthop |-> 1, val |-> 0, nxthop |-> 2] :> 1 @@
                                       [res |-> 1, lasthop |-> 1, val |-> 0, nxthop |-> 0] :> 1 ))
       (* 7th initial condition *)
       \/ /\ trust = Chng(Chng(trust0,<<0,1>>,1),
                                      <<0,2>>,1)
          /\ buf = Chng(buf0,0,([res |-> 0, lasthop |-> 1, val |-> 1] :> 1))
          /\ chan = Chng(chan0,<<2,1>>,<<[src |-> 2, pr |-> 0, res |-> 0]>>)
          /\ track = track0

CreateByz(mal) ==
    /\ BagCardinality(buf[mal]) < BufBound
    /\ \E pkt \in [res : Resource]
        \cup [res : Resource, pr : Priority, src : {mal}]
        (* \cup {"Malformed"}  *):
        /\ \/ buf' = [buf EXCEPT ![mal] = @ (+) SetToBag({pkt})]
    /\ UNCHANGED <<chan, track, trust>>

RcvByz(mal) ==
    /\ BagCardinality(buf[mal]) < BufBound
    /\ \E p \in Peers \ {mal} :
        /\ chan[p,mal] # << >>
        /\ chan' = [chan EXCEPT ![p,mal] = Tail(@)]
        /\ buf' = [buf EXCEPT ![mal] = @ (+) SetToBag({Head(chan[p,mal])})]
    /\ UNCHANGED <<track, trust>>

SendByz(mal) ==
    /\ \E p \in Peers \ {mal} :
       \E pkt \in BagToSet(buf[mal]) :
        /\ chan' = [chan EXCEPT ![mal,p] = Append(@,pkt)]
        /\ buf' = [buf EXCEPT ![mal] = @ (-) SetToBag({pkt})]
    /\ UNCHANGED <<track, trust>>

TypeInv ==
    /\ Peer(0)!TypeInv
    /\ \A p1 \in Peers :
       \A p2 \in Peers :
       \A i \in 1..Len(chan[p1,p2]) :
        chan[p1,p2][i] \in [res : Resource]
         \cup [res : Resource, pr : Priority, src : Peers]
         (* \cup {"Malformed"} *)

Next ==
    \/ /\ TRUE
       /\ \E h \in Honest : Peer(h)!Next
    \/ \E b \in Byzantine : SendByz(b)
    \/ \E b \in Byzantine : CreateByz(b)
    \/ \E b \in Byzantine : RcvByz(b)


(* as long as buf is not empty, processing of any packet should be possible,
   this means no corner cases are unhandled *)
AllPktsEnabled == []( Peer(0)!AllPktsEnabled )
(* this constrains the model checking space *)
ChanSize == \A p1 \in Peers : \A p2 \in Peers : Len(chan[p1,p2]) <= 1
(* BufSize == BagCardinality(buf[0]) <= 1 *)
(* these properties should all fail individually during model checking *)
Never == (* []( *)
     /\ TRUE
     (* there are paths where buf is nonempty *)
     (* /\ buf[0] = EmptyBag *)
     (* there are paths where track is nonempty *)
     (* /\ track[0] = EmptyBag *)
     (* there are paths that make trust nonzero *)
     (* /\ \A p \in Peers : trust[0,p] = 0 *)
(* ) *)
(* Constraint == PickSuccessor(FALSE) *)
--------------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars
================================================================================
