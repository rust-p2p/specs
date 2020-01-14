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
    \/ /\ buf = [p \in Peers |-> EmptyBag]
       /\ track = [p \in Peers |-> EmptyBag]
       /\ trust = [e \in Peers \X Peers |-> TrustBound]
       /\ chan = [e \in Peers \X Peers |-> << >>]
    (* different initial conditions for more complete coverage report *)
    (* 2nd initial condition *)
    \/ /\ trust = ( <<0, 0>> :> 0 @@
                    <<0, 1>> :> 1 @@
                    <<0, 2>> :> 1 @@
                    <<1, 0>> :> 0 @@
                    <<1, 1>> :> 0 @@
                    <<1, 2>> :> 0 @@
                    <<2, 0>> :> 0 @@
                    <<2, 1>> :> 0 @@
                    <<2, 2>> :> 0 )
       /\ buf = (0 :> << >> @@ 1 :> << >> @@ 2 :> ([res |-> 1, lasthop |-> 1] :> 1))
       /\ chan = ( <<0, 0>> :> <<>> @@
                   <<0, 1>> :> <<>> @@
                   <<0, 2>> :> <<>> @@
                   <<1, 0>> :> <<>> @@
                   <<1, 1>> :> <<>> @@
                   <<1, 2>> :> <<>> @@
                   <<2, 0>> :> <<>> @@
                   <<2, 1>> :> <<[src |-> 2, pr |-> 0, res |-> 0]>> @@
                   <<2, 2>> :> <<>> )
       /\ track = ( 0 :> ([res |-> 1, lasthop |-> 2, val |-> 0, nxthop |-> 0] :> 1) @@
                    1 :> << >> @@
                    2 :> ( [res |-> 0, lasthop |-> 1, val |-> 0, nxthop |-> 2] :> 1 @@
                           [res |-> 1, lasthop |-> 1, val |-> 0, nxthop |-> 0] :> 1 ) )
    (* 3nd initial condition *)
    \/ /\ trust = ( <<0, 0>> :> 0 @@
                    <<0, 1>> :> 1 @@
                    <<0, 2>> :> 1 @@
                    <<1, 0>> :> 0 @@
                    <<1, 1>> :> 0 @@
                    <<1, 2>> :> 0 @@
                    <<2, 0>> :> 0 @@
                    <<2, 1>> :> 0 @@
                    <<2, 2>> :> 0 )
       /\ buf = (0 :> ([res |-> 1, lasthop |-> 1] :> 1) @@ 1 :> << >> @@ 2 :> << >>)
       /\ chan = ( <<0, 0>> :> <<>> @@
                   <<0, 1>> :> <<>> @@
                   <<0, 2>> :> <<>> @@
                   <<1, 0>> :> <<>> @@
                   <<1, 1>> :> <<>> @@
                   <<1, 2>> :> <<>> @@
                   <<2, 0>> :> <<>> @@
                   <<2, 1>> :> <<[src |-> 2, pr |-> 0, res |-> 0]>> @@
                   <<2, 2>> :> <<>> )
       /\ track = ( 0 :> ([res |-> 1, lasthop |-> 2, val |-> 0, nxthop |-> 0] :> 1) @@
                    1 :> << >> @@
                    2 :> ( [res |-> 0, lasthop |-> 1, val |-> 0, nxthop |-> 2] :> 1 @@
                           [res |-> 1, lasthop |-> 1, val |-> 0, nxthop |-> 0] :> 1 ) )
    (* 4nd initial condition *)
    \/ /\ trust = [e \in Peers \X Peers |-> 0]
       /\ buf = (0 :> ([res |-> 0, lasthop |-> 1] :> 1) @@ 1 :> <<>> @@ 2 :> <<>>)
       /\ chan = [e \in Peers \X Peers |-> << >>]
       /\ track = ( 0 :> ( [res |-> 1, lasthop |-> 2, val |-> 0, nxthop |-> 0] :> 1 @@
                           [res |-> 1, lasthop |-> 1, val |-> 1, nxthop |-> 2] :> 1 ) @@
                    1 :> <<>> @@
                    2 :>
                    ( [res |-> 0, lasthop |-> 1, val |-> 0, nxthop |-> 2] :> 1 @@
                    [res |-> 1, lasthop |-> 1, val |-> 0, nxthop |-> 0] :> 1 ) )
    (* 5nd initial condition *)
    \/ /\ trust = [e \in Peers \X Peers |-> 0]
       /\ buf = (0 :> ([res |-> 0, lasthop |-> 1, val |-> 0] :> 1) @@ 1 :> <<>> @@ 2 :> <<>>)
       /\ chan = [e \in Peers \X Peers |-> << >>]
       /\ track = ( 0 :> <<>> @@
                    1 :> <<>> @@
                    2 :> <<>>)
    (* (\* 6nd initial condition *\) *)
    (* \/ /\ trust = [e \in Peers \X Peers |-> 0] *)
    (*    /\ buf = (0 :> ([res |-> 0, lasthop |-> 0, val |-> 0] :> 1 @@ [res |-> 1, lasthop |-> 0, val |-> 0] :> 1) @@ 1 :> <<>> @@ 2 :> <<>>) *)
    (*    /\ chan = [e \in Peers \X Peers |-> << >>] *)
    (*    /\ track = ( 0 :> <<>> @@ *)
    (*                 1 :> <<>> @@ *)
    (*                 2 :> <<>>) *)

TypeInv ==
    /\ Peer(0)!TypeInv

Next ==
    \/ /\ TRUE
       (* checking for certain properties, IN this CASE the Never properties, is
          sped up remarkably by reordering the actions *)
       /\ Peer(0)!Next
       /\ \E p \in Peers \ {0} : \E rqst \in Request : \E pkt \in BagToSet(buf[p]) : Peer(p)!Relay(pkt) \cdot Peer(p)!CreateRqst(rqst)
       /\ \E p \in Peers \ {0} : \E pkt \in BagToSet(buf[p]) : Peer(p)!Relay(pkt)

       (* /\ \E p \in Peers : Peer(p)!Next *)

(* as long as buf is not empty, processing of any packet should be possible,
   this means no corner cases are unhandled *)
AllPktsEnabled == []( Peer(0)!AllPktsEnabled )
(* this constrains the model checking space *)
ChanSize == \A p1 \in Peers : \A p2 \in Peers : Len(chan[p1,p2]) <= 1
(* these properties should all fail individually during model checking *)
Never == (* []( *)
     /\ TRUE
     (* there are paths where buf is nonempty *)
     (* /\ buf[0] = EmptyBag *)
     (* all elements are eventually in the buffer *)
     (* tlc doesn't seem to make any progress checking this property *)
     /\ \E e \in [lasthop : {0}, val : Value, res : Resource \ {0}] (* \cup[lasthop : Peers \ {0}, res : Resource \ {0}] *) : []( e \notin BagToSet(buf[0]) )
     (* there are paths where track is nonempty *)
     (* /\ track[0] = EmptyBag *)
     (* there are paths that make trust nonzero *)
     (* /\ \A p \in Peers : trust[0,p] = 0 *)
(* ) *)
--------------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars
================================================================================
