---- MODULE SlidingWindow ----
EXTENDS Naturals, Sequences

CONSTANTS MaxMsgs, MaxMsgsTransit, MaxSeqNum, StartWinSize, Payload, PacketType
VARIABLE msgs, seq_num, send_win, recv_win, channels

vars == <<msgs, seq_num, send_win, recv_win, channels>>
Node == 0..1

ASSUME "data" \in PacketType /\ "ack" \in PacketType

Max(a, b) == IF a > b THEN a ELSE b

----
\* Packet definition

SeqNum == 0..MaxSeqNum
NextSeqNum(sn) == IF sn = MaxSeqNum THEN 0 ELSE sn + 1

Packet == [type: PacketType, seq_num: SeqNum, payload: Payload]

DataPacket(sn, p) == [type |-> "data", seq_num |-> sn, payload |-> p]

AckPacket(sn) ==
    LET p == CHOOSE p \in Payload : TRUE
    IN [type |-> "ack", seq_num |-> sn, payload |-> p]

----
\* Window definition

Remove[seq \in Seq(Packet), elem \in Packet] ==
    IF seq = << >>
    THEN << >>
    ELSE LET head == Head(seq)
             tail == Remove[Tail(seq), elem]
         IN IF head = elem THEN tail ELSE <<head>> \o tail

Filter[seq \in Seq(Packet), sn \in SeqNum] ==
    IF seq = << >>
    THEN << >>
    ELSE LET head == Head(seq)
             tail == Filter[Tail(seq), sn]
         IN IF head.seq_num < sn THEN tail ELSE <<head>> \o tail

Window == [base: SeqNum, size: SeqNum, packets: Seq(Packet)]

WindowInit == [base |-> 0, size |-> StartWinSize, packets |-> << >>]

SeqNumIn(win, sn) ==
    IF win.base + win.size <= MaxSeqNum
    THEN sn >= win.base /\ sn < win.base + win.size
    ELSE \/ sn >= win.base /\ sn <= MaxSeqNum
         \/ sn < win.base + win.size - MaxSeqNum - 1

PacketIn(win, sn) ==
    \E n \in 1..Len(win.packets) : win.packets[n].seq_num = sn

PacketFrom(win) ==
    LET sn == CHOOSE n \in 1..Len(win.packets) : TRUE
    IN win.packets[sn]

InsertPacket(win, p) ==
    IF /\ SeqNumIn(win, p.seq_num)
       /\ ~PacketIn(win, p.seq_num)
    THEN [win EXCEPT !.packets = Append(@, p)]
    ELSE win

DeliverPackets[win \in Window, packets \in Seq(Payload)] ==
    IF PacketIn(win, win.base)
    THEN LET n == CHOOSE n \in 1..Len(win.packets) : win.packets[n].seq_num = win.base
             p == win.packets[n]
             nwin == [win EXCEPT !.base = NextSeqNum(@), !.packets = Remove[@, p]]
             npackets == <<p>> \o packets
         IN DeliverPackets[nwin, packets]
    ELSE <<win, packets>>

WindowInv(win) ==
    /\ Len(win.packets) <= win.size
    /\ \A n \in 1..Len(win.packets) : SeqNumIn(win, win.packets[n].seq_num)

----

LOCAL Socket == INSTANCE Socket WITH Payload <- Packet
LOCAL Channel == INSTANCE Channel

Init ==
    /\ Socket!Init
    /\ channels = [n \in Node |-> Channel!ChannelInit]
    /\ seq_num = [n \in Node |-> 0]
    /\ send_win = [n \in Node |-> WindowInit]
    /\ recv_win = [n \in Node |-> WindowInit]

TypeInv ==
    /\ Socket!TypeInv
    /\ \A n \in Node : Channel!TypeInv(channels[n])
    /\ seq_num \in [Node -> SeqNum]
    /\ send_win \in [Node -> Window]
    /\ recv_win \in [Node -> Window]
    /\ \A n \in Node : WindowInv(send_win[n])
    /\ \A n \in Node : WindowInv(recv_win[n])

Constraint ==
    /\ Socket!Constraint
    /\ \A n \in Node : Channel!Constraint(channels[n])

----

SendMsg(n, d) ==
    /\ SeqNumIn(send_win[n], seq_num[n])
    /\ seq_num' = [seq_num EXCEPT ![n] = NextSeqNum(@)]
    /\ LET packet == DataPacket(seq_num[n], d)
           win == InsertPacket(send_win[n], packet)
           msg == Socket!Msg(n, 1 - n, packet)
       IN /\ send_win' = [send_win EXCEPT ![n] = win]
          /\ msgs' = Socket!Send(msgs, msg)
    /\ channels' = [channels EXCEPT ![n] = Channel!Send(@, d)]
    /\ UNCHANGED recv_win

ReSendMsg(n) ==
    /\ send_win[n].packets # << >>
    /\ LET packet == PacketFrom(send_win[n])
           msg == Socket!Msg(n, 1 - n, packet)
       IN msgs' = Socket!Send(msgs, msg)
    /\ UNCHANGED <<seq_num, send_win, recv_win, channels>>

SendAck(n) ==
    /\ LET packet == AckPacket(recv_win[n].base)
           msg == Socket!Msg(n, 1 - n, packet)
       IN msgs' = Socket!Send(msgs, msg)
    /\ UNCHANGED <<seq_num, send_win, recv_win, channels>>

RecvMsg(n) ==
    /\ Socket!RecvEn(n, 1 - n)
    /\ LET msg == Socket!PeekRecv(n, 1 - n)
           packet == msg.payload
       IN /\ \/ /\ packet.type = "data"
                /\ LET res == DeliverPackets[InsertPacket(recv_win[n], packet), << >>]
                   IN /\ recv_win' = [recv_win EXCEPT ![n] = res[1]]
                      /\ channels' = [channels EXCEPT ![1 - n] = [@ EXCEPT !.recvQ = @ \o res[2]]]
                /\ UNCHANGED send_win
             \/ /\ packet.type = "ack"
                /\ LET base == Max(packet.seq_num, send_win[n].base)
                       win == [send_win[n] EXCEPT !.base = base, !.packets = Filter[@, base]]
                   IN send_win' = [send_win EXCEPT ![n] = win]
                /\ UNCHANGED <<recv_win, channels>>
          /\ msgs' = Socket!Recv(msgs, msg)
    /\ UNCHANGED seq_num

NodeNext(n) ==
    \/ \E d \in Payload : SendMsg(n, d)
    \/ ReSendMsg(n)
    \/ SendAck(1 - n)
    \/ RecvMsg(1 - n)

Next ==
    \/ NodeNext(0)
    \/ Socket!Fail /\ UNCHANGED <<seq_num, send_win, recv_win, channels>>

Liveness == \A n \in Node : Channel!Liveness(channels[n])

Spec == Init /\ [][Next]_vars /\ Liveness
====
