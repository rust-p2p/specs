---- MODULE TestPeer -----------------------------------------------------
EXTENDS Sequences, Naturals, TLC, Peer
(* Documentation *)
(* This module builds a state machine that executes a sequence of tests. *)
(* In order to adapt to different module than 'Incentives', change 'Incentives' to the *)
(* module to test, adapt number of tests by adding T's in TestInit, and adapt the *)
(* operators Pre, Run and the sequence P according to example *)
--------------------------------------------------------------------------------
VARIABLE Tests, counter, done, state
testvars == <<Tests, counter, done, state>>

total == <<Tests, counter, done, state>> \o vars

(* e == CHOOSE elt \in Peers \X Peers : elt[1] # elt[2] *)
(* h0 == e[1] *)
(* h1 == e[2] *)
(* r0 == CHOOSE elt \in Resource : TRUE *)

(* how many tests to run in total *)
n == 1

Init ==
    /\ buf = [p \in Peers |-> EmptyBag]
    /\ track = [p \in Peers |-> EmptyBag]
    /\ trust = [e \in Peers \X Peers |-> TrustBound]
    /\ chan = [e \in Peers \X Peers |-> << >>]

TestInit ==
    /\ Tests = <<>>
    /\ counter = 1
    /\ done = 0
    /\ state = 0
    /\ Init

(* Test1 *)
Pre1 ==
    /\ counter = 1
    /\ trust' = ( <<0, 0>> :> 2 @@
             <<0, 1>> :> 2 @@
             <<0, 2>> :> 2 @@
             <<1, 0>> :> 2 @@
             <<1, 1>> :> 2 @@
             <<1, 2>> :> 2 @@
             <<2, 0>> :> 2 @@
             <<2, 1>> :> 2 @@
             <<2, 2>> :> 2 )
    /\ buf' = (0 :> ([res |-> 2, lasthop |-> 1] :> 3) @@ 1 :> << >> @@ 2 :> << >>)
    /\ chan' = ( <<0, 0>> :> <<>> @@
                 <<0, 1>> :> <<[src |-> 0, pr |-> 0, res |-> 2]>> @@
                 <<0, 2>> :> <<>> @@
                 <<1, 0>> :> <<>> @@
                 <<1, 1>> :> <<>> @@
                 <<1, 2>> :> <<>> @@
                 <<2, 0>> :> <<>> @@
                 <<2, 1>> :> <<>> @@
                 <<2, 2>> :> <<>> )
    /\ track' = ( 0 :> ([res |-> 2, lasthop |-> 1, val |-> 0, nxthop |-> 0] :> 2) @@
                  1 :> ([res |-> 2, lasthop |-> 0, val |-> 0, nxthop |-> 1] :> 1) @@
                  2 :> << >> )


Run1 ==
    /\ counter = 1
    (* /\ Print(BagCardinality(Peer(0)!PNeeds),TRUE) *)
    (* /\ Print(BagCardinality(track[0]),TRUE) *)
    /\ Print(unneeded,TRUE)
    (* /\ Print(maxusable,TRUE) *)
    (* /\ Print(rplys_in_buf,TRUE) *)
    (* /\ Print(Filter(RplyInBuf,([res |-> 2,lasthop |-> 0] :> 1)),TRUE) *)
    (* /\ Print(Filter(RplyInBuf,([res |-> 2, lasthop |-> 1] :> 3)),TRUE) *)
    (* /\ Print(buf[0],TRUE) *)
    /\ UNCHANGED vars

Post1 ==
    /\ TRUE

Pre ==
    /\ state = 0
    (* CHANGE: add setup for different tests *)
    /\ \/ Pre1
       (* \/ Pre2 *)
    /\ state' = 1
    /\ UNCHANGED <<Tests, counter,done>>

Run ==
    /\ state = 1
    (* CHANGE: Add operators/functions to test *)
    /\ \/ Run1
       (* \/ Run2 *)
    /\ state' = 2
    /\ UNCHANGED <<Tests, counter,done>>

(* CHANGE: Add postcondition to P *)
PList == <<Post1>>

Post ==
    /\ state = 2
    /\ counter \in 1..Len(PList)
    /\ UNCHANGED vars
    /\ Tests' = Tests \o <<IF PList[counter] THEN "passed" ELSE "failed">>
    /\ state' = 0
    /\ IF counter = n THEN /\ done' = 1
                           /\ UNCHANGED counter
                      ELSE /\ counter' = counter + 1
                           /\ UNCHANGED done

Test ==
    \/ /\ done = 0
       /\ \/ Pre
          \/ Run
          \/ Post
          \/ /\ ~ ENABLED Pre
             /\ counter \in 1..n
             /\ state = 0
             /\ Print("Precondition not enabled, Test:", TRUE)
             /\ Print(counter, TRUE)
             /\ done' = 2
             /\ UNCHANGED <<state,Tests, counter>>
             /\ UNCHANGED vars
          \/ /\ ~ ENABLED Run
             /\ counter \in 1..n
             /\ state = 1
             /\ Print("Run statement not enabled, Test:", TRUE)
             /\ Print(counter, TRUE)
             /\ done' = 2
             /\ UNCHANGED <<state,Tests, counter>>
             /\ UNCHANGED vars
          \/ /\ ~ ENABLED Post
             /\ counter \in 1..n
             /\ state = 2
             /\ Print("Postcondition not enabled, Test:", TRUE)
             /\ Print(counter, TRUE)
             /\ done' = 2
             /\ UNCHANGED <<state,Tests, counter>>
             /\ UNCHANGED vars
    \/ /\ done = 1
       (* /\ \A i \in 1..n : /\ Print(i,TRUE) *)
       (*                             /\ Print(Tests[i], TRUE) *)
       /\ done' = 2
       /\ UNCHANGED <<state,Tests, counter>>
       /\ UNCHANGED vars

TestSpec == TestInit /\ [][Test]_total
================================================================================
