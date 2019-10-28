---- MODULE Handshake ----

EXTENDS Naturals, Sequences, UnreliableChannel

CONSTANT MaxN

VARIABLES aState, bState, a2b, b2a

\* Start sequence number
SSn == 1..MaxN

\* Sequence number
Sn == 0..(MaxN + 3)

\* Stage
Stage == 0..4

\* State contains the role and the random sequence number of the handshake.
State == [r: BOOLEAN, n: Sn, s: Stage]

\* A message has drf set to true iff it's the first message of a handshake.
Message == [drf: BOOLEAN, n: Sn]

\* The initial state.
Init ==
    /\ aState = [r |-> FALSE, n |-> 0, s |-> 0]
    /\ bState = aState
    /\ a2b = << >>
    /\ b2a = a2b

\* The type invariant.
TypeInv ==
    /\ aState \in State
    /\ bState \in State
    /\ a2b \in Seq(Message)
    /\ b2a \in Seq(Message)

\* Start picks a random sequence number and sets role to initiator.
Start(state, n) ==
    /\ n > 0
    /\ state.s = 0
    /\ state' = [r |-> TRUE, n |-> n, s |-> 1]
    /\ UNCHANGED <<a2b, b2a>>

\* Sends the first message of the handshake.
SendStage1(state, sCh) ==
    /\ state.r = TRUE /\ state.s = 1                      \* Enabled iff state = 1 and role is initiator.
    /\ sCh' =
        LET p == [drf |-> TRUE, n |-> state.n]            \* Send the first packet
        IN Append(sCh, p)
    /\ UNCHANGED state

\* Recv the rist message of the handshake.
RecvStage1(state, rCh, tie) ==
    /\ rCh # << >>
    /\ state.s < 2                                        \* Enabled iff state = 0 (responder)
    /\ Head(rCh).drf
    /\ rCh' = Tail(rCh)                                   \* or state = 1 (concurrent initiator).
    /\ state' =
        LET p == Head(rCh)                                \* stage1 packet
            r == /\ state.s = 1                           \* Iff we initiated and the sequence number
                 /\ \/ state.n > p.n
                    \/ /\ state.n = p.n
                       /\ tie
            n == IF r THEN state.n ELSE p.n               \* is larger we remain initiator.
            s == 2
        IN [r |-> r, n |-> n, s |-> s]

SendStage2(state, sCh) ==
    /\ state.s = 2
    /\ sCh' =
        LET p == [drf |-> FALSE, n |-> state.n + 1]
        IN Append(sCh, p)
    /\ UNCHANGED state

RecvStage2(state, rCh) ==
    /\ rCh # << >>
    /\ state.s = 1
    /\ rCh' = Tail(rCh)
    /\ state' =
        LET p == Head(rCh)
            s == IF ~p.drf /\ p.n = state.n + 1 THEN 3 ELSE state.s
        IN [state EXCEPT !.s = s]

SendStage3(state, sCh) ==
    /\ state.s = 3
    /\ sCh' =
        LET p == [drf |-> FALSE, n |-> state.n + 2]
        IN Append(sCh, p)
    /\ UNCHANGED state

RecvStage3(state, rCh) ==
    /\ rCh # << >>
    /\ state.s = 2
    /\ rCh' = Tail(rCh)
    /\ state' =
        LET p == Head(rCh)
            s == IF ~p.drf /\ p.n = state.n + 2 THEN 4 ELSE state.s
        IN [state EXCEPT !.s = s]

Send(state, sCh) ==
    /\ state.s = 4
    /\ sCh' =
        LET p == [drf |-> FALSE, n |-> state.n + 3]
        IN Append(sCh, p)
    /\ UNCHANGED state

Recv(state, rCh) ==
    /\ \/ state.s = 4
       \/ (state.s = 3 /\ ~state.r)
    /\ rCh # << >>
    /\ state' = [state EXCEPT !.s = 4]
    /\ rCh' = Tail(rCh)

Liveness ==
    /\ aState # 4 ~> aState.s = 4
    /\ bState # 4 ~> bState.s = 4
    /\ (aState.s = 4 /\ bState.s = 4 => aState.n = bState.n)

Next ==
    \/ \E n \in SSn : Start(aState, n) /\ UNCHANGED bState
    \/ \E n \in SSn : Start(bState, n) /\ UNCHANGED aState

    \/ SendStage1(aState, a2b) /\ UNCHANGED <<bState, b2a>>
    \/ SendStage1(bState, b2a) /\ UNCHANGED <<aState, a2b>>

    \/ RecvStage1(aState, b2a, TRUE) /\ UNCHANGED <<bState, a2b>>
    \/ RecvStage1(bState, a2b, FALSE) /\ UNCHANGED <<aState, b2a>>

    \/ SendStage2(aState, a2b) /\ UNCHANGED <<bState, b2a>>
    \/ SendStage2(bState, b2a) /\ UNCHANGED <<aState, a2b>>

    \/ RecvStage2(aState, b2a) /\ UNCHANGED <<bState, a2b>>
    \/ RecvStage2(bState, a2b) /\ UNCHANGED <<aState, b2a>>

    \/ SendStage3(aState, a2b) /\ UNCHANGED <<bState, b2a>>
    \/ SendStage3(bState, b2a) /\ UNCHANGED <<aState, a2b>>

    \/ RecvStage3(aState, b2a) /\ UNCHANGED <<bState, a2b>>
    \/ RecvStage3(bState, a2b) /\ UNCHANGED <<aState, b2a>>

    \/ Send(aState, a2b) /\ UNCHANGED <<bState, b2a>>
    \/ Send(bState, b2a) /\ UNCHANGED <<aState, a2b>>

    \/ Recv(aState, b2a) /\ UNCHANGED <<bState, a2b>>
    \/ Recv(bState, a2b) /\ UNCHANGED <<aState, b2a>>

    \/ Fail(a2b) /\ UNCHANGED <<aState, bState, b2a>>
    \/ Fail(b2a) /\ UNCHANGED <<aState, bState, a2b>>

Spec == Init /\ [][Next]_<<aState, bState, a2b, b2a>> /\ Liveness

====
