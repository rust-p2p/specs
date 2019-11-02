---- MODULE Socket ----
EXTENDS Bags, Naturals

CONSTANTS Node, MaxMsgsTransit, Payload
VARIABLE msgs

Packet == [src: Node, dst: Node, payload: Payload]

Init ==
    /\ msgs = EmptyBag

TypeInv ==
    /\ IsABag(msgs)
    /\ \A msg \in BagToSet(msgs) : msg \in Packet

Constraint == BagCardinality(msgs) <= MaxMsgsTransit

Send(ms, m) == ms \oplus SetToBag({m})

Recv(ms, m) == ms \ominus SetToBag({m})

----
\* Socket methods

Msg(n, to, payload) == [src |-> n, dst |-> to, payload |-> payload]

RecvEn(n, from) ==
    \E msg \in BagToSet(msgs) :
        /\ msg.src = from
        /\ msg.dst = n

PeekRecv(n, from) ==
    CHOOSE msg \in BagToSet(msgs) :
        /\ msg.src = from
        /\ msg.dst = n

----
\* Error conditions

LOCAL Dup ==
    /\ BagToSet(msgs) # {}
    /\ LET msg == CHOOSE m \in BagToSet(msgs) : TRUE
       IN msgs' = Send(msgs, msg)

LOCAL Loose ==
    /\ BagToSet(msgs) # {}
    /\ LET msg == CHOOSE m \in BagToSet(msgs) : TRUE
       IN msgs' = Recv(msgs, msg)

Fail == Dup \/ Loose

====
