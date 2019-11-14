---- MODULE Socket ----
EXTENDS Naturals, Sequences

CONSTANTS Node, MaxMsgsTransit, Payload
VARIABLE msgs

Packet == [src: Node, dst: Node, payload: Payload]

Init ==
    /\ msgs = << >>

TypeInv ==
    /\ msgs \in Seq(Packet)

Constraint == Len(msgs) <= MaxMsgsTransit

Send(ms, m) == Append(ms, m)

LOCAL Remove(ms, i) ==
    [j \in 1..(Len(ms) - 1) |->
        IF j >= i THEN ms[j + 1] ELSE ms[j]]

Recv(ms, i) == Remove(ms, i)

----
\* Socket methods

Msg(n, to, payload) == [src |-> n, dst |-> to, payload |-> payload]

RecvEn(n, from) ==
    \E i \in 1..Len(msgs) :
        /\ msgs[i].src = from
        /\ msgs[i].dst = n

PeekRecv(n, from) ==
    LET i == CHOOSE i \in 1..Len(msgs) :
        /\ msgs[i].src = from
        /\ msgs[i].dst = n
    IN i

----
\* Error conditions

LOCAL Dup ==
    /\ msgs # << >>
    /\ msgs' = Append(msgs, Head(msgs))

LOCAL Loose ==
    /\ msgs # << >>
    /\ msgs' = Tail(msgs)

LOCAL Trans ==
    /\ Len(msgs) > 1
    /\ msgs' = <<msgs[2], msgs[1]>> \o Tail(Tail(msgs))

LOCAL Shift1 ==
    /\ Len(msgs) > 1
    /\ msgs' = [i \in 1..Len(msgs) |->
        IF i = Len(msgs)
        THEN msgs[1]
        ELSE msgs[i + 1]
       ]

\* Trans and Shift1 are capable of producing all permutations.
Fail == Dup \/ Loose \/ Trans \/ Shift1

====
