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

h0 == P
h1 == CHOOSE elt \in Peers \ {P} : TRUE
r0 == CHOOSE elt \in Resources : TRUE

T ==
    [state |-> 0,
    status |-> "not tested"]


TestInit ==
    (* CHANGE: how many tests in total *)
    /\ Tests = <<T,T,T,T,T,T,T,T,T>>
    /\ counter = 1
    /\ done = 0
    /\ Init

(* Test1, tests if Rcv performs as expected *)
Pre1 ==
    /\ counter = 1
    /\ UNCHANGED vars


Run1 ==
    /\ counter = 1
    /\ CreateRqstArg(h0,[src |-> h0, dst |-> h1, pr |-> 4, res |-> r0])

Post1 ==
    /\ TRUE
(* End of Test1 *)

(* Test2*)
Pre2 ==
    /\ counter = 2
    /\ UNCHANGED vars

Run2 ==
    /\ counter = 2
    /\ Rcv(h0,h1)

Post2 ==
    /\ buf[h1,rqst] = ( <<[src |-> h0, dst |-> h1, pr |-> 4, res |-> r0],0>> :> 1)

Pre3 ==
    /\ counter = 3
    /\ UNCHANGED vars

Run3 ==
    /\ counter = 3
    /\ Rply(h1)

Post3 ==
    /\ TRUE

Pre4 ==
    /\ counter = 4
    /\ UNCHANGED vars

Run4 ==
    /\ counter = 4
    /\ Rcv(h1,h0)

Post4 ==
    /\ TRUE

Pre5 ==
    /\ counter = 5
    /\ UNCHANGED vars

Run5 ==
    /\ counter = 5
    (* /\ Print(MatchesWithIn(0,own[0]), TRUE) *)
    /\ ConsumeRply(h0)

Post5 ==
    /\ TRUE

Pre6 ==
    /\ counter = 6
    /\ trust' = (<<P, P>> :> 2 @@ <<P, h1>> :> 0 @@ <<h1, P>> :> 0 @@ <<h1, h1>> :> 2)
    /\ relay' = (P :> ([src |-> h1, dst |-> P, pr |-> 0, res |-> r0] :> 1) @@ h1 :> << >>)
    /\ own' = (P :> ([pr |-> 0, res |-> r0] :> 1) @@ h1 :> ([pr |-> 0, res |-> r0] :> 1))
    /\ buf' = ( <<P, 1>> :> (<<[src |-> h1, dst |-> P, pr |-> 0, res |-> r0], 0>> :> 1) @@
               <<P, 2>> :> << >> @@
               <<h1, 1>> :> (<<[src |-> P, dst |-> h1, pr |-> 0, res |-> r0], 0>> :> 1) @@
               <<h1, 2>> :> << >> )
    /\ chan' = (P :> <<[src |-> P, dst |-> h1, pr |-> 0, res |-> r0]>> @@ h1 :> <<>>)

Run6 ==
    /\ counter = 6
    (* /\ Print(MatchesWithIn(0,own[0]), TRUE) *)
    (* /\ ENABLED Rcv(h0,h1) *)
    /\ \E pkt \in Request : \E min \in BagToSet(buf[h1,rqst]) : min[2] < EffPriority(h1,pkt)
   (* /\ Rcv(0,[src |-> 1, dst |-> 0, res |-> 0]) *)
    /\ UNCHANGED <<buf, chan, own, relay, trust>>

Post6 ==
    /\ TRUE

Pre7 ==
    /\ counter = 7
    /\ trust' = (<<h0, h0>> :> 2 @@ <<h0, h1>> :> 0 @@ <<h1, h0>> :> 0 @@ <<h1, h1>> :> 2)
    /\ relay' = (h0 :> << >> @@ h1 :> << >>)
    /\ own' = (h0 :> ([pr |-> 0, res |-> r0] :> 1) @@ h1 :> << >>)
    /\ buf' = ( <<h0, 1>> :> << >> @@
                <<h0, 2>> :> << >> @@
                <<h1, 1>> :> << >> @@
                <<h1, 2>> :> << >> )
    /\ chan' = (h0 :> <<[src |-> h0, dst |-> h1, pr |-> 0, res |-> r0]>> @@ h1 :> <<>>)

Run7 ==
    /\ counter = 7
    /\ ENABLED RcvRqstLowLoad(h1,Head(chan[P]))
    /\ UNCHANGED <<buf, chan, own, relay, trust>>

Post7 ==
    /\ TRUE

Pre8 ==
    /\ counter = 8
    /\ trust' = (<<h0, h0>> :> 2 @@ <<h0, h1>> :> 1 @@ <<h1, h0>> :> 1 @@ <<h1, h1>> :> 2)
    /\ relay' = (h0 :> << >> @@ h1 :> << >>)
    /\ own' = (h0 :> << >> @@ h1 :> ([pr |-> 0, res |-> r0] :> 1))
    /\ buf' = ( <<h0, 1>> :> << >> @@
               <<h0, 2>> :> ([src |-> h1, dst |-> h0, res |-> r0] :> 1) @@
               <<h1, 1>> :> << >> @@
               <<h1, 2>> :> ([src |-> h0, dst |-> h1, res |-> r0] :> 1) )
    /\ chan' = (h0 :> <<[src |-> h0, dst |-> h1, res |-> r0]>> @@ h1 :> <<>>)


Run8 ==
    /\ counter = 8
    /\ ~ ENABLED RcvRplyLimit(h1,Head(chan[P]))
    /\ UNCHANGED <<buf, chan, own, relay, trust>>

Post8 ==
    /\ TRUE

Pre9 ==
    /\ counter = 9
    /\ trust' = (<<h0, h0>> :> 3 @@ <<h0, h1>> :> 0 @@ <<h1, h0>> :> 2 @@ <<h1, h1>> :> 3)
    /\ relay' = ( h0 :> ([src |-> h1, dst |-> h0, pr |-> 0, res |-> r0] :> 1) @@
                  h1 :> ([src |-> h0, dst |-> h1, pr |-> 0, res |-> r0] :> 1) )
    /\ own' = (h0 :> ([pr |-> 0, res |-> r0] :> 1) @@ h1 :> ([pr |-> 0, res |-> r0] :> 2))
    /\ buf' = ( <<h0, 1>> :> << >> @@
                <<h0, 2>> :> << >> @@
                <<h1, 1>> :> << >> @@
                <<h1, 2>> :> ([src |-> h0, dst |-> h1, res |-> r0] :> 2) )
    /\ chan' = ( h0 :> <<[src |-> h0, dst |-> h1, res |-> r0]>> @@
                 h1 :> <<[src |-> h1, dst |-> h0, pr |-> 0, res |-> r0]>> )


Run9 ==
    /\ counter = 9
    (* /\ ENABLED RcvRply(h1,Head(chan[P])) *)
    /\ ENABLED RcvRplyLimit(h1,Head(chan[P]))
    /\ UNCHANGED <<buf, chan, own, relay, trust>>

Post9 ==
    /\ TRUE

Pre ==
    /\ Tests[counter].state = 0
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
       \/ Run6
       \/ Run7
       \/ Run8
       \/ Run9
    /\ Tests' = [Tests EXCEPT ![counter].state = 2]
    /\ UNCHANGED <<counter,done>>

(* CHANGE: Add postcondition to P *)
PList == <<Post1, Post2, Post3, Post4, Post5, Post6, Post7, Post8, Post9>>

Post ==
    /\ Tests[counter].state = 2
    /\ counter \in 1..Len(PList)
    /\ UNCHANGED vars
    /\ Tests' = [Tests EXCEPT ![counter].status = IF PList[counter] THEN "passed"
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
