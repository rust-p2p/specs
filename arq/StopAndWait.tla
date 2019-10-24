---- MODULE StopAndWait ----
\* This specification describes a protocol for using lossy FIFO transmission
\* lines to transmit a sequence of values from a sender to a receiver. The
\* sender sends a data value d by sending a sequence of (b, d) messages on
\* msgQ, where b is a control bit. It knows that the message has been received
\* when it receives the ack b from the receiver on ackQ. It sends the next
\* value with a different control bit. The receiver knows that a message on
\* msgQ contains a new value when the control bit differs from the last one it
\* received. The receiver keeps sending the last control bit it received on
\* ackQ.
EXTENDS Naturals, Sequences
CONSTANT Data \* The set of data values that can be sent

VARIABLES
    \* The sequence of <control bit, data value> messages in transit to the
    \* receiver.
    msgQ,
    \* The sequence of one-bit acknowledgments in transit to the sender.
    ackQ,
    \* The last control bit sent by the sender; it is complemented when sending
    \*  a new data value
    sBit,
    \* The last acknowledgment bit received by the sender.
    sAck,
    \* The last control bit received by the receiver.
    rBit,
    \* The last value sent by the sender.
    sent,
    \* The last value received by the receiver.
    recv

----

\* The initial condition:
\*   Both message queues are empty.
\*   All the bits equal 0 or 1 and are equal to each other.
\*   The initial values for sent and recv are arbitrary data values.
Init ==
    /\ msgQ = <<>>
    /\ ackQ = <<>>
    /\ sBit \in {0, 1}
    /\ sAck = sBit
    /\ rBit = sBit
    /\ sent \in Data
    /\ recv \in Data

\* The type correctness invariant.
TypeInv ==
    /\ msgQ \in Seq({0, 1} \X Data)
    /\ ackQ \in Seq({0, 1})
    /\ sBit \in {0, 1}
    /\ sAck \in {0, 1}
    /\ rBit \in {0, 1}
    /\ sent \in Data
    /\ recv \in Data

----

\* The action in which the sender sends a new data value.
SendMsg(d) ==
    /\ sAck = sBit                        \* Enabled iff sAck equals sBit.
    /\ sent' = d                          \* Set sent to d.
    /\ sBit' = 1 - sBit                   \* Complement control bit sBit.
    /\ msgQ' = Append(msgQ, <<sBit', d>>) \* Send value on msgQ with new control bit.
    /\ UNCHANGED <<ackQ, sAck, rBit, recv>>

\* The sender resends the last message it sent on msgQ.
ReSendMsg ==
    /\ sAck # sBit                           \* Enabled iff sAck doesn't equal sBit.
    /\ msgQ' = Append(msgQ, <<sBit, sent>>)  \* Resend the last value in send.
    /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, recv>>

\* The receiver receives the message at the head of msgQ.
RecvMsg ==
    /\ msgQ # << >>                          \* Enabled iff msgQ not empty.
    /\ msgQ' = Tail(msgQ)                    \* Remove message from head of msgQ.
    /\ rBit' = Head(msgQ)[1]                 \* Set rBit to message's control bit.
    /\ recv' = Head(msgQ)[2]                 \* Set recv to message's data value.
    /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

\* The receiver sends rBit on ackQ at any time.
SendAck ==
    /\ ackQ' = Append(ackQ, rBit)
    /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, recv>>

\* The sender receives an ack on ackQ
RecvAck ==
    /\ ackQ # << >>
    /\ ackQ' = Tail(ackQ)
    /\ sAck' = Head(ackQ)
    /\ UNCHANGED <<msgQ, sBit, rBit, sent, recv>>

\* The action of loosing a message from queue q.
\* Leaves every variable unchanged except msgQ and ackQ
Lose(q) ==
    /\ q # << >>            \* Enabled iff q is not empty
    /\ \E i \in 1..Len(q) : \* For some i, remote the ith message from q.
        q' = [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]
    /\ UNCHANGED <<sBit, sAck, rBit, sent, recv>>

\* Lose a message from msgQ.
LoseMsg == Lose(msgQ) /\ UNCHANGED ackQ

\* Loose a message from ackQ.
LoseAck == Lose(ackQ) /\ UNCHANGED msgQ

\* The next state action.
Next ==
    \/ \E d \in Data : SendMsg(d)
    \/ ReSendMsg
    \/ RecvMsg
    \/ SendAck
    \/ RecvAck
    \/ LoseMsg
    \/ LoseAck

----

\* The tuple of all variables.
vars == <<msgQ, ackQ, sBit, sAck, rBit, sent, recv>>

\* The liveness condition
Fairness ==
    /\ WF_vars(ReSendMsg)
    /\ WF_vars(SendAck)
    /\ SF_vars(RecvMsg)
    /\ SF_vars(RecvAck)

\* The complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Correctess proofs
THEOREM Spec => []TypeInv
====
