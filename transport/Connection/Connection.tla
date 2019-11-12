---- MODULE Connection ----
EXTENDS BoundedTimer, Naturals, Sequences

CONSTANTS MaxMsgs, MaxMsgsTransit, MaxSeqNum, StartWinSize, Payload,
          SIT, RIT
VARIABLES msgs, channels, seq_num, send_win, recv_win,
          state, sit, rit

channel_vars == <<msgs, channels, seq_num, send_win, recv_win>>
vars == <<msgs, channels, seq_num, send_win, recv_win, state, sit, rit>>

PacketType == {"open", "data", "ack"}

LOCAL Channel == INSTANCE SlidingWindow

State == {"open", "closed"}

----
Init ==
    /\ Channel!Init
    /\ state = [n \in Channel!Node |-> "closed"]
    /\ sit = [n \in Channel!Node |-> MaxTimer]
    /\ rit = [n \in Channel!Node |-> MaxTimer]

TypeInv ==
    /\ Channel!TypeInv
    /\ state \in [Channel!Node -> State]
    /\ sit \in [Channel!Node -> Timer]
    /\ rit \in [Channel!Node -> Timer]

Constraint == Channel!Constraint

Open(n) ==
    /\ state[n] = "closed"
    /\ state' = [state EXCEPT ![n] = "open"]
    /\ sit' = [sit EXCEPT ![n] = SIT]
    /\ rit' = [rit EXCEPT ![n] = RIT]
    /\ seq_num' = [seq_num EXCEPT ![n] = 0]
    /\ send_win' = [send_win EXCEPT ![n] = Channel!WindowInit]
    /\ recv_win' = [recv_win EXCEPT ![n] = Channel!WindowInit]
    /\ UNCHANGED <<msgs, channels>>

Close(n) ==
    /\ state[n] = "open"
    /\ state' = [state EXCEPT ![n] = "closed"]
    /\ sit' = [sit EXCEPT ![n] = SIT]
    /\ rit' = [rit EXCEPT ![n] = RIT]
    /\ seq_num' = [seq_num EXCEPT ![n] = 0]
    /\ send_win' = [send_win EXCEPT ![n] = Channel!WindowInit]
    /\ recv_win' = [recv_win EXCEPT ![n] = Channel!WindowInit]
    /\ UNCHANGED <<msgs, channels>>

SendMsg(n, d) ==
    /\ state[n] = "open"
    /\ ~TimedOut(sit[n])
    /\ Channel!SendMsg(n, d)
    /\ sit' = [sit EXCEPT ![n] = SIT]
    /\ UNCHANGED <<state, rit>>

ReSendMsg(n) ==
    /\ state[n] = "open"
    /\ ~TimedOut(sit[n])
    /\ Channel!ReSendMsg(n)
    /\ UNCHANGED <<state, sit, rit>>

SendAck(n) ==
    /\ state[n] = "open"
    /\ ~TimedOut(rit[n])
    /\ Channel!SendAck(n)
    /\ UNCHANGED <<state, sit, rit>>

RecvMsg(n) ==
    /\ state[n] = "open"
    /\ ~TimedOut(rit[n])
    /\ Channel!RecvMsg(n)
    /\ rit' = [rit EXCEPT ![n] = RIT]
    /\ UNCHANGED <<state, sit>>

SitTimeout(n) ==
    /\ state[n] = "open"
    /\ TimedOut(sit[n])
    /\ Close(n)

RitTimeout(n) ==
    /\ state[n] = "open"
    /\ TimedOut(rit[n])
    /\ Close(n)

Tick(n) ==
    /\ Enabled(sit[n]) \/ Enabled(rit[n])
    /\ sit' = [sit EXCEPT ![n] = TimerTick(sit[n])]
    /\ rit' = [rit EXCEPT ![n] = TimerTick(rit[n])]
    /\ UNCHANGED channel_vars
    /\ UNCHANGED state

NodeNext(n) ==
    \/ Open(n)
    \/ \E d \in Payload : SendMsg(n, d)
    \/ ReSendMsg(n)
    \/ SendAck(1 - n)
    \/ RecvMsg(1 - n)
    \/ SitTimeout(n)
    \/ RitTimeout(1 - n)

Fail ==
    /\ Channel!Fail
    /\ UNCHANGED <<state, sit, rit>>

Next ==
    \/ NodeNext(0)
    \/ Fail
    \/ Tick(0)
    \/ Tick(1)

Liveness == Channel!Liveness

Spec == Init /\ [][Next]_vars /\ Liveness
====
