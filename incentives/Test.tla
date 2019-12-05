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
    passed |-> "not tested"]


TestInit ==
    (* CHANGE: how many tests in total *)
    /\ Tests = <<T(* ,T,T *)>>
    /\ counter = 1
    /\ done = 0
    /\ Init

Pre ==
    /\ Tests[counter].state = 0
    (* CHANGE: add setup for different tests *)
    /\ \/ /\ counter = 1
          /\ q_out' = [q_out EXCEPT ![0] = <<[src |-> 0, dst |-> 1, type |-> 1, pr |-> 4, res |-> 0]>>]
          /\ UNCHANGED <<b_in,trust,relaytable>>
       (* \/ /\ counter = 2 *)
       (*    /\ q_out' = [q_out EXCEPT ![0] = <<2>>] *)
       (*    /\ UNCHANGED <<trust, b_in, relaytable>> *)
    /\ Tests' = [Tests EXCEPT ![counter].state = 1]
    /\ UNCHANGED <<counter,done>>

Run ==
    /\ Tests[counter].state = 1
    (* CHANGE: Add operators/functions to test *)
    /\ \/ /\ counter = 1
          /\ Send(0)
          (* /\ UNCHANGED vars *)
       (* \/ /\ counter = 2 *)
       (*    /\ *)
       (*    /\ UNCHANGED <<trust, b_in, relaytable>> *)
    /\ Tests' = [Tests EXCEPT ![counter].state = 2]
    /\ UNCHANGED <<counter,done>>

(* CHANGE: Add a postcondition *)
Post1 ==
    /\ b_in[1,1] = (<<[src |-> 0, dst |-> 1, type |-> 1, pr |-> 4, res |-> 0],0>> :> 1)
    /\ b_in[1,2] = EmptyBag
    /\ b_in[0,1] = EmptyBag
    /\ b_in[0,2] = EmptyBag
Post2 == q_out[0] = <<>>
(* CHANGE: Add postcondition to P *)
P == <<Post1, Post2>>

Post ==
    /\ Tests[counter].state = 2
    /\ counter \in 1..Len(P)
    /\ UNCHANGED vars
    /\ Tests' = [Tests EXCEPT ![counter].passed = IF P[counter] THEN "passed"
                                                                ELSE "failed"]
    /\ IF counter = Len(Tests) THEN /\ done' = 1
                                    /\ UNCHANGED <<counter>>
                               ELSE /\ counter' = counter + 1
                                    /\ UNCHANGED <<done>>

Test ==
    \/ /\ done = 0
       /\ \/ Pre
          \/ /\ ~ ENABLED Pre
             /\ Tests[counter].state = 0
             /\ Print("Precondition not enabled, counter:", TRUE)
             /\ Print(counter, TRUE)
             /\ UNCHANGED <<Tests, counter>>
             /\ UNCHANGED vars
          \/ Run
          \/ /\ ~ ENABLED Run
             /\ Tests[counter].state = 1
             /\ Print("Run statement not enabled, counter:", TRUE)
             /\ Print(counter, TRUE)
             /\ UNCHANGED <<Tests, counter>>
             /\ UNCHANGED vars
          \/ Post
          \/ /\ ~ ENABLED Post
             /\ Tests[counter].state = 2
             /\ Print("Postcondition not enabled, counter:", TRUE)
             /\ Print(counter, TRUE)
             /\ UNCHANGED <<Tests, counter>>
             /\ UNCHANGED vars
    \/ /\ done = 1
       /\ \A i \in 1..Len(Tests) : /\ Print(i,TRUE)
                                   /\ Print(Tests[i].passed, TRUE)
       /\ done' = 2
       /\ UNCHANGED <<Tests, counter>>
       /\ UNCHANGED vars

TestSpec == TestInit /\ [][Test]_total
================================================================================
