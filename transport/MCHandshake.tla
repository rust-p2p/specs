---- MODULE MCHandshake ----
EXTENDS Handshake
CONSTANTS a2bLen, b2aLen

QueueLenConstraint ==
    /\ Len(a2b) <= a2bLen
    /\ Len(b2a) <= b2aLen

====
