---- MODULE Socket ----
EXTENDS Bags, Naturals

CONSTANT Node, MaxMsgsTransit
VARIABLE msgs

Packet(T) == [src: Node, dst: Node, payload: T]

SocketInit ==
    /\ msgs = EmptyBag

SocketTypeInv(T) ==
    /\ IsABag(msgs)
    /\ \A msg \in BagToSet(msgs) : msg \in Packet(T)

SocketConstraint == BagCardinality(msgs) <= MaxMsgsTransit

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

Dup ==
    /\ BagToSet(msgs) # {}
    /\ LET msg == CHOOSE m \in BagToSet(msgs) : TRUE
       IN msgs' = Send(msgs, msg)

Loose ==
    /\ BagToSet(msgs) # {}
    /\ LET msg == CHOOSE m \in BagToSet(msgs) : TRUE
       IN msgs' = Recv(msgs, msg)

Fail == Dup \/ Loose

====
