---- MODULE GoBackN ----
\* This specification describes a protocol for using lossy, duplicating and
\* reordering  transmission lines to transmit a sequence of values from a
\* sender to a receiver. The sender sends a data value d by sending a sequence
\* of (sn, d) messages on msgQ, where sn is a sequence number. The receiver
\* requests more data by sending the sn it wants to receive on ackQ.
\*
\* In this model we assume that sequence numbers are unbounded and the window
\* size is constant.
EXTENDS Naturals, Sequences, UnreliableChannel

CONSTANTS
    Data, \* The set of data values that can be sent
    N     \* window size

VARIABLES
    \* The sequence of <control bit, data value> messages in transit to the
    \* receiver.
    msgQ,
    \* The sequence of one-bit acknowledgments in transit to the sender.
    ackQ,
    \* The last sequence number sent.
    sSn,
    \* The sender window.
    sWin,
    \* The receiver window.
    rWin

ASSUME N \in Nat /\ N > 0

\* Types
Sn == Nat
Packet == [sn: Sn, d: Data]
Win == [base: Sn, max: Sn, q: Seq(Packet)]

\* Contains takes a sequence and a predicate and evaluates to true if any
\* element of the sequence satisfies the predicate.
Contains(seq, p) == \E i \in 1..Len(seq): p[seq[i]]

\* Filter takes a sequence and a predicate and returns a sequence containing
\* only the elements where predicate evaluates to true.
Filter[seq \in Seq(Packet), sn \in Sn] ==
    IF seq = <<>>
    THEN <<>>
    ELSE
        LET tail == Filter[Tail(seq), sn]
        IN IF Head(seq).sn < sn
           THEN tail
           ELSE <<Head(seq)>> \o tail

\* Insert takes a sequence, a predicate and an element and inserts the
\* element before the first element satisfying the predicate.
Insert[seq \in Seq(Packet), p \in Packet] ==
    IF seq = <<>>
    THEN <<p>>
    ELSE
        IF Head(seq).sn > p.sn
        THEN <<p>> \o seq
        ELSE <<Head(seq)>> \o Insert[Tail(seq), p]

\* Moves the window to b.
WinMove[w \in Win, b \in Sn] == [base |-> b, max |-> b + N, q |-> w.q]

\* Moves the window until all ordered messages are removed.
WinMoveOrdered[w \in Win] ==
    IF w.q # <<>> /\ w.base = Head(w.q).sn
    THEN WinMoveOrdered[[WinMove[w, w.base + 1] EXCEPT !.q = Tail(w.q)]]
    ELSE w

\* Moves the window and removes acked messages.
WinMoveBase[w \in Win, b \in Sn] ==
    LET nw == WinMove[w, b]
        nq == Filter[nw.q, nw.base]
    IN [nw EXCEPT !.q = nq]

\* Inserts a message into the receive window.
WinInsert[w \in Win, p \in Packet] ==
    IF /\ w.base <= p.sn                                  \* If the sequence number is in the window
       /\ p.sn <= w.max
       /\ ~Contains(w.q, [q \in Packet |-> q.sn = p.sn])  \* and the packet isn't a duplicate.
    THEN
        [w EXCEPT !.q = Insert[@, p]]                     \* Insert the packet before a packet with a
                                                          \* larger sequence number.
    ELSE w

----

\* The initial condition:
\*   Both message queues are empty.
\*   All the sequence numbers equal 0.
\*   The initial value for recv is an arbitrary data values.
Init ==
    /\ msgQ = <<>>
    /\ ackQ = <<>>
    /\ sSn = 0
    /\ sWin = [base |-> 0, max |-> N, q |-> <<>>]
    /\ rWin = sWin

\* Invariant describing the relationship of the fields in a window.
WindowInv(w) ==
    /\ w.max >= w.base
    /\ w.max - w.base = N
    /\ Len(w.q) <= w.max - w.base
    /\ \A i \in 1..Len(w.q) :
        /\ w.q[i].sn >= w.base
        /\ w.q[i].sn <= w.max

\* The type correctness invariant.
TypeInv ==
    /\ msgQ \in Seq(Packet)
    /\ ackQ \in Seq(Sn)
    /\ sSn \in Sn
    /\ sWin \in Win
    /\ WindowInv(sWin)
    /\ rWin \in Win
    /\ WindowInv(rWin)

----

\* The action in which the sender sends a new data value.
SendMsg(d) ==
    /\ sSn < sWin.max                                   \* Enabled iff there is still credit in the window.
    /\ sSn' = sSn + 1                                   \* Increment the sequence number.
    /\ LET p == [sn |-> sSn, d |-> d]
       IN
        /\ sWin' = [sWin EXCEPT !.q = Append(sWin.q, p)]\* Add packet to the window.
        /\ msgQ' = Append(msgQ, p)                      \* Send value on msgQ with sequence number.
    /\ UNCHANGED <<ackQ, rWin>>

\* The sender resends a message from the window on msgQ.
ReSendMsg(i) ==
    /\ i <= Len(sWin.q)                                 \* Enabled iff the index is in range.
    /\ msgQ' = Append(msgQ, sWin.q[i])                  \* Resend the ith message from the window.
    /\ UNCHANGED <<ackQ, sSn, sWin, rWin>>

\* The sender resends any message from the window on msgQ.
ReSendAnyMsg == \E i \in 1..Len(sWin.q) : ReSendMsg(i)

\* The receiver receives the message at the head of msgQ.
RecvMsg ==
    /\ msgQ # << >>                          \* Enabled iff msgQ not empty.
    /\ msgQ' = Tail(msgQ)                    \* Remove message from head of msgQ.
    /\ rWin' = WinMoveOrdered[WinInsert[rWin, Head(msgQ)]]
        \* Inserts the packet into the window if it is not a duplicate and filters
        \*  any complete sequences of packets from the window.
    /\ UNCHANGED <<ackQ, sSn, sWin>>

\* The receiver sends receiver window base on ackQ at any time.
SendAck ==
    /\ ackQ' = Append(ackQ, rWin.base)
    /\ UNCHANGED <<msgQ, sSn, sWin, rWin>>

\* The sender receives an ack on ackQ
RecvAck ==
    /\ ackQ # << >>                    \* Enabled iff ackQ not empty.
    /\ ackQ' = Tail(ackQ)              \* Remove ack from head of ackQ.
    /\ sWin' =                         \* Iff ack larger than base move sWin
        IF Head(ackQ) > sWin.base      \* to new base (and drop all acked messages).
        THEN WinMoveBase[sWin, Head(ackQ)]
        ELSE sWin
    /\ UNCHANGED <<msgQ, sSn, rWin>>

\* Message queue failure.
MsgQFail == Fail(msgQ) /\ UNCHANGED <<ackQ, sSn, sWin, rWin>>

\* Ack queue failure.
AckQFail == Fail(ackQ) /\ UNCHANGED <<msgQ, sSn, sWin, rWin>>

\* The next state action.
Next ==
    \/ /\ sSn < 4 \* TODO remove this purely mc constraint
       /\ \E d \in Data : SendMsg(d)
    \/ ReSendAnyMsg
    \/ RecvMsg
    \/ SendAck
    \/ RecvAck
    \/ MsgQFail
    \/ AckQFail

----

\* The tuple of all variables.
vars == <<msgQ, ackQ, sSn, sWin, rWin>>

\* The liveness condition
Fairness ==
    /\ WF_vars(ReSendAnyMsg)
    /\ WF_vars(SendAck)
    /\ SF_vars(RecvMsg)
    /\ SF_vars(RecvAck)

\* The complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Correctess proofs
THEOREM Spec => []TypeInv
====
