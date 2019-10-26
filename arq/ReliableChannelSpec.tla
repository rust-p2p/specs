---- MODULE ReliableChannelSpec ----
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES sendQ, recvQ

Init ==
    /\ sendQ = << >>
    /\ recvQ = << >>

TypeInv ==
    /\ sendQ \in Seq(Data)
    /\ recvQ \in Seq(Data)
    /\ Len(recvQ) <= Len(sendQ)
    /\ \A i \in 1..Len(recvQ) : recvQ[i] = sendQ[i]

Send(m) == sendQ' = Append(sendQ, m)

Recv(m) == recvQ' = Append(recvQ, m)

Liveness == Len(sendQ) > Len(recvQ) ~> Len(sendQ) = Len(recvQ)

====
