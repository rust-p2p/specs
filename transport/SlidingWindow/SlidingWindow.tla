---- MODULE SlidingWindow ----
EXTENDS Naturals, Sequences

CONSTANTS MaxMsgsTransit, MaxSeqNum, StartWinSize, Payload, PacketType
VARIABLE msgs, seq_num, send_win, recv_win

vars == <<msgs, seq_num, send_win, recv_win>>
Node == 0..1

ASSUME "data" \in PacketType /\ "ack" \in PacketType

----
\* Packet definition

SeqNum == 0..MaxSeqNum
NextSeqNum(sn) == IF sn = MaxSeqNum THEN 0 ELSE sn + 1

Packet == [type: PacketType, seq_num: SeqNum, payload: Payload]
----
\* Window definition

Remove[seq \in Seq(Packet), elem \in Packet] ==
    IF seq = << >>
    THEN << >>
    ELSE LET head == Head(seq)
             tail == Remove[Tail(seq), elem]
         IN IF head = elem THEN tail ELSE Append(head, tail)

Window == [base: SeqNum, size: SeqNum, packets: Seq(Packet)]

WindowInit == [base |-> 0, size |-> StartWinSize, packets |-> << >>]

SeqNumIn(win, sn) ==
    IF win.base + win.size <= MaxSeqNum
    THEN sn >= win.base /\ sn < win.base + win.size
    ELSE \/ sn >= win.base /\ sn <= MaxSeqNum
         \/ sn >= 0 /\ sn < win.base + win.size - MaxSeqNum

PacketIn(win, sn) ==
    \E n \in 1..Len(win.packets) : win.packets[n].seq_num = sn

WindowInv(win) ==
    /\ Len(win.packets) <= win.size
    /\ \A n \in 1..Len(win.packets) : SeqNumIn(win, n)

InsertPacket(win, p) ==
    IF /\ SeqNumIn(win, p.seq_num)
       /\ ~PacketIn(win, p.seq_num)
    THEN [win EXCEPT !.packets = Append(@, p)]
    ELSE win

DeliverPackets[win \in Window] ==
    IF PacketIn(win, win.base)
    THEN LET n == CHOOSE n \in 1..Len(win.packets) : win.packets[n].seq_num = win.base
             p == win.packets[n]
             nwin == [win EXCEPT !.base = NextSeqNum(@), !.packets = Remove[@, p]]
         IN DeliverPackets[nwin]
    ELSE win

----

LOCAL Socket == INSTANCE Socket WITH Payload <- Packet

Init ==
    /\ Socket!Init
    /\ seq_num = [n \in Node |-> 0]
    /\ send_win = [n \in Node |-> WindowInit]
    /\ recv_win = [n \in Node |-> WindowInit]

TypeInv ==
    /\ Socket!TypeInv
    /\ seq_num \in [Node -> SeqNum]
    /\ send_win \in [Node -> Window]
    /\ recv_win \in [Node -> Window]
    /\ \A n \in Node : WindowInv(send_win[n])
    /\ \A n \in Node : WindowInv(recv_win[n])

Constraint ==
    /\ Socket!Constraint

----

NodeNext(n) ==
    /\ LET p == CHOOSE p \in Packet : TRUE
           w == recv_win[n]
           x == InsertPacket(w, p)
           y == DeliverPackets[x]
       IN recv_win' = [recv_win EXCEPT ![n] = y]
    /\ UNCHANGED <<msgs, seq_num, send_win>>

Next ==
    \/ \E n \in Node : NodeNext(n)
    \/ Socket!Fail

Spec == Init /\ [][Next]_vars
====
