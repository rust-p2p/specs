---- MODULE TestMCPeer -----------------------------------------------------
EXTENDS Sequences, Naturals, TLC, MCPeer
(* Documentation *)
(* This module builds a state machine that executes a sequence of tests. *)
(* In order to adapt to different module than 'Incentives', change 'Incentives' to the *)
(* module to test, adapt number of tests by adding T's in TestInit, and adapt the *)
(* operators Pre, Run and the sequence P according to example *)
--------------------------------------------------------------------------------
VARIABLE Tests, counter, done, state
testvars == <<Tests, counter, done, state>>

total == <<Tests, counter, done, state>> \o vars

e == CHOOSE elt \in Peers \X Peers : elt[1] # elt[2]
h0 == e[1]
h1 == e[2]
r0 == CHOOSE elt \in Resource : TRUE

(* T == *)
(*     [state |-> 0, *)
(*     status |-> "not tested"] *)
n == 9

TestInit ==
    (* CHANGE: how many tests in total *)
    /\ Tests = <<(* T,T,T,T,T,T,T,T,T,T,T,T *)>>
    /\ counter = 1
    /\ done = 0
    /\ state = 0
    /\ Init

(* Test1, tests if Rcv performs as expected *)
Pre1 ==
    /\ counter = 1
    /\ UNCHANGED vars


Run1 ==
    /\ counter = 1
    /\ Peer(0)!CreateRqst([src |-> 0, pr |-> 2, res |-> 1])

Post1 ==
    /\ TRUE
(* End of Test1 *)

(* Test2 *)
Pre2 ==
    /\ counter = 2
    /\ UNCHANGED vars

Run2 ==
    /\ counter = 2
    (* /\ Peer(h0)!Rcv(h0) \cdot Peer(h0)!CreateRqst([src |-> h0, pr |-> 4, res |-> r0]) *)
    (* /\ Peer(h0)!CreateRqst([src |-> h0, pr |-> 4, res |-> r0]) *)
    /\ UNCHANGED vars

Post2 ==
    /\ TRUE
(* End of Test2 *)
(* Test3 *)
Pre3 ==
    /\ counter = 3
    /\ UNCHANGED vars

Run3 ==
    /\ counter = 3
    /\ Peer(0)!Rcv(0)

Post3 ==
    /\ TRUE
(* End of Test3 *)

(* Test4 *)
Pre4 ==
    /\ counter = 4
    /\ UNCHANGED vars

Run4 ==
    /\ counter = 4
    /\ Peer(0)!Relay([lasthop |-> 0, val |-> 2, res |-> 1])

Post4 ==
    /\ TRUE
(* End of Test4 *)
(* Test5 *)
Pre5 ==
    /\ counter = 5
    /\ UNCHANGED vars

Run5 ==
    /\ counter = 5
    /\ Peer(1)!Rcv(0)

Post5 ==
    /\ TRUE

(* Test6 *)
Pre6 ==
    /\ counter = 6
    /\ UNCHANGED vars

Run6 ==
    /\ counter = 6
    /\ Peer(1)!Rply([res |-> 1, lasthop |-> 0, val |-> 2])

Post6 ==
    /\ TRUE

(* Test7 *)
Pre7 ==
    /\ counter = 7
    /\ UNCHANGED vars

Run7 ==
    /\ counter = 7
    /\ Peer(0)!Rcv(1)

Post7 ==
    /\ TRUE

(* Test8 *)
Pre8 ==
    /\ counter = 8
    /\ UNCHANGED vars

Run8 ==
    /\ counter = 8
    /\ Peer(0)!Consume([res |-> 1, lasthop |-> 1])

Post8 ==
    /\ TRUE


(* Test9: Does stealing of packets work properly? *)
Pre9 ==
   LET S == Peers \X Peers
   IN
   (* \E t \in [e \in S -> {0..TrustBound}] *)
    /\ counter = 9
    /\ trust' \in 0..3
    /\ buf' = [p \in Peers |-> EmptyBag]
    /\ chan' = ( <<0, 0>> :> <<>> @@
                 <<0, 1>> :> <<[src |-> 0, pr |-> 0, res |-> 2]>> @@
                 <<0, 2>> :> <<>> @@
                 <<1, 0>> :> <<>> @@
                 <<1, 1>> :> <<>> @@
                 <<1, 2>> :> <<>> @@
                 <<2, 0>> :> <<>> @@
                 <<2, 1>> :> <<>> @@
                 <<2, 2>> :> <<>> )
    /\ track' = ( 0 :> ([res |-> 2, lasthop |-> 1, val |-> 0, nxthop |-> 1] :> 3) @@
                  1 :> ([res |-> 2, lasthop |-> 0, val |-> 0, nxthop |-> 1] :> 1) @@
                  2 :> << >> )


Run9 ==
    /\ counter = 9
    (* /\ Print(BagCardinality(Peer(0)!PNeeds),TRUE) *)
    (* /\ Print(BagCardinality(track[0]),TRUE) *)
    (* /\ Print(Peer(0)!unneeded,TRUE) *)
    (* /\ Print(Peer(0)!unneeded,TRUE) *)
    (* /\ Print(Peer(0)!maxusable,TRUE) *)
    (* /\ Print(Peer(0)!rplys_in_buf,TRUE) *)
    (* /\ Print(Peer(0)!Filter(Peer(0)!RplyInBuf,[lasthop |-> 0,res |-> 0] :> 1),TRUE) *)
    (* /\ Print(buf[0],TRUE) *)
    /\ UNCHANGED vars

Post9 ==
    /\ TRUE

Pre ==
    /\ state = 0
    (* CHANGE: add setup for different tests *)
    /\ \/ Pre1
       \/ Pre2
       \/ Pre3
       \/ Pre4
       \/ Pre5
       \/ Pre6
       \/ Pre7
       \/ Pre8
       \/ Pre9
    /\ state' = 1
    /\ UNCHANGED <<Tests, counter,done>>

Run ==
    /\ state = 1
    (* CHANGE: Add operators/functions to test *)
    /\ \/ Run1
       \/ Run2
       \/ Run3
       \/ Run4
       \/ Run5
       \/ Run6
       \/ Run7
       \/ Run8
       \/ Run9
    /\ state' = 2
    /\ UNCHANGED <<Tests, counter,done>>

(* CHANGE: Add postcondition to P *)
PList == <<Post1, Post2, Post3, Post4, Post5, Post6, Post7, Post8, Post9>>

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
