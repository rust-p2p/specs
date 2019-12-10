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
    /\ Tests = <<T(* ,T,T *)>>
    /\ counter = 1
    /\ done = 0
    /\ Init

(* First Test, tests if Send(_) adds the packet to the queue, changing nothing else *)
Pre1 ==
    /\ counter = 1
    /\ out' = [out EXCEPT ![0] = <<[src |-> 0, dst |-> 1, type |-> 1, pr |-> 4, res |-> 0]>>]
    /\ UNCHANGED <<own,in,trust,relay,n>>

Run1 ==
    /\ counter = 1
    /\ Send(0,[src |-> 0, dst |-> 1, type |-> 1, pr |-> 4, res |-> 0])
    /\ UNCHANGED <<own,in,trust,relay,n>>
    (* /\ Rcv(1,[src |-> 0, dst |-> 1, type |-> 1, pr |-> 4, res |-> 0]) *)

Post1 ==
    /\ in[1,1] = (<<[src |-> 0, dst |-> 1, type |-> 1, pr |-> 4, res |-> 0],0>> :> 1)
    /\ in[1,2] = EmptyBag
    /\ in[0,1] = EmptyBag
    /\ in[0,2] = EmptyBag

(* Pre2 == *)
(*     /\ counter = 2 *)
(*     /\  *)
    (* /\ UNCHANGED vars *)
Pre2 ==
       /\ counter = 2
       /\ out' = [out EXCEPT ![0] = <<[src |-> 0, dst |-> 1, type |-> 1, pr |-> 2, res |-> 0]>>]
       /\ UNCHANGED <<own,in,trust,relay,n>>

Run2 ==
    /\ UNCHANGED vars

Post2 == out[0] = <<>>

Pre ==
    /\ Tests[counter].state = 0
    (* CHANGE: add precondition of test *)
    /\ \/ Pre1
       \/ Pre2
    /\ Tests' = [Tests EXCEPT ![counter].state = 1]
    /\ UNCHANGED <<counter,done>>

Run ==
    /\ Tests[counter].state = 1
    (* CHANGE: Add operators/functions to test *)
    /\ \/ Run1
       \/ Run2
    /\ Tests' = [Tests EXCEPT ![counter].state = 2]
    /\ UNCHANGED <<counter,done>>

(* CHANGE: Add a postcondition *)

(* CHANGE: Add postcondition to P *)
P == <<Post1, Post2>>

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
          (* \/ /\ ~ ENABLED Pre *)
          (*    /\ Tests[counter].state = 0 *)
          (*    /\ Print("Precondition not enabled, counter:", TRUE) *)
          (*    /\ Print(counter, TRUE) *)
          (*    /\ done' = 2 *)
          (*    /\ UNCHANGED <<Tests, counter>> *)
          (*    /\ UNCHANGED vars *)
          (* \/ /\ ~ ENABLED Run *)
          (*    /\ Tests[counter].state = 1 *)
          (*    /\ Print("Run statement not enabled, counter:", TRUE) *)
          (*    /\ Print(counter, TRUE) *)
          (*    /\ done' = 2 *)
          (*    /\ UNCHANGED <<Tests, counter>> *)
          (*    /\ UNCHANGED vars *)
          (* \/ /\ ~ ENABLED Post *)
          (*    /\ Tests[counter].state = 2 *)
          (*    /\ Print("Postcondition not enabled, counter:", TRUE) *)
          (*    /\ Print(counter, TRUE) *)
          (*    /\ done' = 2 *)
          (*    /\ UNCHANGED <<Tests, counter>> *)
          (*    /\ UNCHANGED vars *)
    \/ /\ done = 1
       /\ \A i \in 1..Len(Tests) : /\ Print(i,TRUE)
                                   (* /\ Print(Tests[i].status, TRUE) *)
       /\ done' = 2
       /\ UNCHANGED <<Tests, counter>>
       /\ UNCHANGED vars

TestSpec == TestInit /\ [][Test]_total
================================================================================
