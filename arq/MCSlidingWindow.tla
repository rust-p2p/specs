---- MODULE MCSlidingWindow ----
EXTENDS SlidingWindow
CONSTANTS sendQLen, msgQLen, ackQLen

QueueLenConstraint ==
    /\ Len(sendQ) <= sendQLen
    /\ Len(msgQ) <= msgQLen
    /\ Len(ackQ) <= ackQLen

====
