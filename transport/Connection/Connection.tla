---- MODULE Connection ----
EXTENDS BoundedTimer, Naturals, Sequences

CONSTANTS MaxMsgs, MaxMsgsTransit, MaxSeqNum, MaxTTL, StartWinSize, Payload,
          SIT, RIT, LINGER
VARIABLES msgs, channels, seq_num, send_win, recv_win,
          state, sit, rit, linger

channel_vars == <<msgs, channels, seq_num, send_win, recv_win>>
vars == <<msgs, channels, seq_num, send_win, recv_win, state, sit, rit>>

PacketType == {"open", "data", "ack"}

LOCAL Channel == INSTANCE SlidingWindow

State == {"open", "linger", "closed"}

----
Init ==
    /\ Channel!Init
    /\ state = [n \in Channel!Node |-> "closed"]
    /\ sit = [n \in Channel!Node |-> MaxTimer]
    /\ rit = [n \in Channel!Node |-> MaxTimer]
    /\ linger = [n \in Channel!Node |-> MaxTimer]

TypeInv ==
    /\ Channel!TypeInv
    /\ state \in [Channel!Node -> State]
    /\ sit \in [Channel!Node -> Timer]
    /\ rit \in [Channel!Node -> Timer]
    /\ linger \in [Channel!Node -> Timer]

Constraint == Channel!Constraint

ResetChannelState(n) ==
    /\ seq_num' = [seq_num EXCEPT ![n] = 0]
    /\ send_win' = [send_win EXCEPT ![n] = Channel!WindowInit]
    /\ recv_win' = [recv_win EXCEPT ![n] = Channel!WindowInit]
    /\ channels' = [channels EXCEPT ![n] = [sendQ |-> << >>, recvQ |-> << >>]]
    /\ UNCHANGED <<msgs>>

Open(n) ==
    /\ state[n] = "closed"
    /\ state' = [state EXCEPT ![n] = "open"]
    /\ sit' = [sit EXCEPT ![n] = SIT]
    /\ rit' = [rit EXCEPT ![n] = RIT]
    /\ linger' = [linger EXCEPT ![n] = MaxTimer]
    /\ UNCHANGED channel_vars

Linger(n) ==
    /\ state[n] = "open"
    /\ state' = [state EXCEPT ![n] = "linger"]
    /\ sit' = [sit EXCEPT ![n] = MaxTimer]
    /\ rit' = [rit EXCEPT ![n] = MaxTimer]
    /\ linger' = [linger EXCEPT ![n] = LINGER]
    /\ UNCHANGED channel_vars

Close(n) ==
    /\ state[n] # "closed"
    /\ state' = [state EXCEPT ![n] = "closed"]
    /\ sit' = [sit EXCEPT ![n] = MaxTimer]
    /\ rit' = [rit EXCEPT ![n] = MaxTimer]
    /\ linger' = [linger EXCEPT ![n] = MaxTimer]
    /\ ResetChannelState(n)

SendMsg(n, d) ==
    /\ state[n] = "open"
    /\ ~TimedOut(sit[n])
    /\ Channel!SendMsg(n, d)
    /\ sit' = [sit EXCEPT ![n] = SIT]
    /\ UNCHANGED <<state, rit, linger>>

ReSendMsg(n) ==
    /\ state[n] = "open"
    /\ ~TimedOut(sit[n])
    /\ Channel!ReSendMsg(n)
    /\ UNCHANGED <<state, sit, rit, linger>>

SendAck(n) ==
    /\ state[n] = "open"
    /\ ~TimedOut(rit[n])
    /\ Channel!SendAck(n)
    /\ UNCHANGED <<state, sit, rit, linger>>

RecvMsg(n) ==
    /\ state[n] = "open"
    /\ ~TimedOut(rit[n])
    /\ Channel!RecvMsg(n)
    /\ rit' = [rit EXCEPT ![n] = RIT]
    /\ UNCHANGED <<state, sit, linger>>

SitTimeout(n) ==
    /\ state[n] = "open"
    /\ TimedOut(sit[n])
    /\ Linger(n)

RitTimeout(n) ==
    /\ state[n] = "open"
    /\ TimedOut(rit[n])
    /\ Close(n)

LingerTimeout(n) ==
    /\ state[n] = "linger"
    /\ TimedOut(linger[n])
    /\ Close(n)

Tick(n) ==
    /\ Enabled(sit[n]) \/ Enabled(rit[n]) \/ Enabled(linger[n]) \/ msgs # << >>
    /\ sit' = [sit EXCEPT ![n] = TimerTick(sit[n])]
    /\ rit' = [rit EXCEPT ![n] = TimerTick(rit[n])]
    /\ linger' = [linger EXCEPT ![n] = TimerTick(linger[n])]
    /\ Channel!Tick
    /\ UNCHANGED <<channels, seq_num, send_win, recv_win, state>>

NodeNext(n) ==
    \/ Open(n)
    \/ \E d \in Payload : SendMsg(n, d)
    \/ ReSendMsg(n)
    \/ SendAck(1 - n)
    \/ RecvMsg(1 - n)
    \/ SitTimeout(n)
    \/ RitTimeout(1 - n)
    \/ LingerTimeout(n)

Fail ==
    /\ Channel!Fail
    /\ UNCHANGED <<state, sit, rit, linger>>

Next ==
    \/ NodeNext(0)
    \/ Fail
    \/ /\ Tick(0)
       /\ Tick(1)
    \/ Open(1)

Liveness == Channel!Liveness

Spec == Init /\ [][Next]_vars /\ Liveness
====
