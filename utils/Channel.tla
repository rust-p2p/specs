---- MODULE Channel ----
EXTENDS Naturals, Sequences

CONSTANT Payload, MaxMsgs

Channel == [sendQ: Seq(Payload), recvQ: Seq(Payload)]

ChannelInit == [sendQ |-> << >>, recvQ |-> << >>]

TypeInv(ch) ==
    /\ ch \in Channel
    /\ Len(ch.recvQ) <= Len(ch.sendQ)
    /\ \A i \in 1..Len(ch.recvQ) : ch.recvQ[i] = ch.sendQ[i]

Constraint(ch) == Len(ch.sendQ) <= MaxMsgs

Send(ch, m) == [ch EXCEPT !.sendQ = Append(@, m)]

Recv(ch, m) == [ch EXCEPT !.recvQ = Append(@, m)]

Liveness(ch) == Len(ch.sendQ) > Len(ch.recvQ) ~> Len(ch.sendQ) = Len(ch.recvQ)

====
