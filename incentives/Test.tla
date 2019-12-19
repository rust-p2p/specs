---- MODULE Test -----------------------------------------------------
EXTENDS Sequences, Naturals, TLC, Incentives
(* Documentation *)
(* This module builds a state machine that executes a sequence of tests. *)
(* In order to adapt to different module than 'Incentives', change 'Incentives' to the *)
(* module to test, adapt number of tests by adding T's in TestInit, and adapt the *)
(* operators Pre, Run and the sequence P according to example *)
--------------------------------------------------------------------------------
VARIABLE Tests, counter, done
testvars == <<Tests, counter, done>>

total == <<Tests, counter, done>> \o vars

T ==
    [state |-> 0,
    status |-> "not tested"]


TestInit ==
    (* CHANGE: how many tests in total *)
    /\ Tests = <<T,T,T,T,T>>
    /\ counter = 1
    /\ done = 0
    /\ Init

(* Test1, tests if Send and Rcv perform as expected *)
Pre1 ==
    /\ counter = 1
    /\ UNCHANGED vars


Run1 ==
    /\ counter = 1
    /\ CreateReq(0,[src |-> 0, dst |-> 1, pr |-> 4, res |-> 0])
   (* /\ UNCHANGED <<trust,in>> *)
      (* /\ UNCHANGED vars *)

Post1 ==
    /\ TRUE
(* End of Test1 *)

(* Test2*)
Pre2 ==
    /\ counter = 2
    /\ UNCHANGED vars

Run2 ==
    /\ counter = 2
    /\ Send(0,[src |-> 0, dst |-> 1, pr |-> 4, res |-> 0])
    /\ Rcv(1,[src |-> 0, dst |-> 1, pr |-> 4, res |-> 0])

Post2 ==
    /\ in[1,1] = ( <<[src |-> 0, dst |-> 1, pr |-> 4, res |-> 0],0>> :> 1)

Pre3 ==
    /\ counter = 3
    /\ UNCHANGED vars

Run3 ==
    /\ counter = 3
    /\ Rply(1)

Post3 ==
    /\ TRUE

Pre4 ==
    /\ counter = 4
    /\ UNCHANGED vars

Run4 ==
    /\ counter = 4
    /\ Send(1,[src |-> 1, dst |-> 0, res |-> 0])
    /\ Rcv(0,[src |-> 1, dst |-> 0, res |-> 0])

Post4 ==
    /\ TRUE

Pre5 ==
    /\ counter = 5
    /\ UNCHANGED vars

Run5 ==
    /\ counter = 5
    (* /\ Print(MatchesWithIn(0,own[0]), TRUE) *)
    /\ ConsumeRply(0)
    (* /\ Rcv(0,[src |-> 1, dst |-> 0, res |-> 0]) *)

Post5 ==
    /\ TRUE

Pre ==
    /\ Tests[counter].state = 0
    (* CHANGE: add setup for different tests *)
    /\ \/ Pre1
       \/ Pre2
       \/ Pre3
       \/ Pre4
       \/ Pre5
    /\ Tests' = [Tests EXCEPT ![counter].state = 1]
    /\ UNCHANGED <<counter,done>>

Run ==
    /\ Tests[counter].state = 1
    (* CHANGE: Add operators/functions to test *)
    /\ \/ Run1
       \/ Run2
       \/ Run3
       \/ Run4
       \/ Run5
    /\ Tests' = [Tests EXCEPT ![counter].state = 2]
    /\ UNCHANGED <<counter,done>>

(* CHANGE: Add postcondition to P *)
P == <<Post1, Post2, Post3, Post4, Post5>>

Post ==
    /\ Tests[counter].state = 2
    /\ counter \in 1..Len(P)
    /\ UNCHANGED vars
    /\ Tests' = [Tests EXCEPT ![counter].status = IF P[counter] THEN "passed"
                                                                ELSE "failed"]
    /\ IF counter = Len(Tests) THEN /\ done' = 1
                                    /\ UNCHANGED <<counter>>
                               ELSE /\ counter' = counter + 1
                                    /\ UNCHANGED <<done>>

Test ==
    \/ /\ done = 0
       /\ \/ Pre
          \/ Run
          \/ Post
          \/ /\ ~ ENABLED Pre
             /\ Tests[counter].state = 0
             /\ Print("Precondition not enabled, Test:", TRUE)
             /\ Print(counter, TRUE)
             /\ done' = 2
             /\ UNCHANGED <<Tests, counter>>
             /\ UNCHANGED vars
          \/ /\ ~ ENABLED Run
             /\ Tests[counter].state = 1
             /\ Print("Run statement not enabled, Test:", TRUE)
             /\ Print(counter, TRUE)
             /\ done' = 2
             /\ UNCHANGED <<Tests, counter>>
             /\ UNCHANGED vars
          \/ /\ ~ ENABLED Post
             /\ Tests[counter].state = 2
             /\ Print("Postcondition not enabled, Test:", TRUE)
             /\ Print(counter, TRUE)
             /\ done' = 2
             /\ UNCHANGED <<Tests, counter>>
             /\ UNCHANGED vars
    \/ /\ done = 1
       /\ \A i \in 1..Len(Tests) : /\ Print(i,TRUE)
                                   /\ Print(Tests[i].status, TRUE)
       /\ done' = 2
       /\ UNCHANGED <<Tests, counter>>
       /\ UNCHANGED vars

TestSpec == TestInit /\ [][Test]_total
================================================================================
