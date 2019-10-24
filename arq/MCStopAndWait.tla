---- MODULE MCStopAndWait ----
EXTENDS StopAndWait
CONSTANTS msgQLen, ackQLen

SeqConstraint ==
    /\ Len(msgQ) <= msgQLen
    /\ Len(ackQ) <= ackQLen

SentLeadsToRecv ==
    \A d \in Data : (sent = d) /\ (sBit # sAck) ~> recv = d

====
