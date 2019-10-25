---- MODULE MCGoBackN ----
EXTENDS GoBackN
CONSTANTS msgQLen, ackQLen

QueueLenConstraint ==
    /\ Len(msgQ) <= msgQLen
    /\ Len(ackQ) <= ackQLen

====
