---- MODULE Ping ----
EXTENDS BoundedTimer, Naturals, Sequences

CONSTANT Node, MaxMsgsTransit
VARIABLES msgs, state, timer

Payload == {"ping", "pong"}
Socket == INSTANCE Socket

State == { "ready", "wait_pong" }

Constraint == Socket!Constraint

Init ==
    /\ Socket!Init
    /\ state = [n \in Node |-> "ready"]
    /\ timer = [n \in Node |-> MaxTimer]

TypeInv ==
    /\ Socket!TypeInv
    /\ state \in [Node -> State]
    /\ timer \in [Node -> Timer]

Ping(n) ==
    /\ state[n] = "ready"
    /\ msgs' = Socket!Send(msgs, Socket!Msg(n, 1 - n, "ping"))
    /\ state' = [state EXCEPT ![n] = "wait_pong"]
    /\ timer' = [timer EXCEPT ![n] = 1]

Pong(n) ==
    /\ Socket!RecvEn(n, 1 - n)
    /\ LET i == Socket!PeekRecv(n, 1 - n)
           rmsg == msgs[i]
           smsg == Socket!Msg(n, 1 - n, "pong")
       IN /\ rmsg.payload = "ping"
          /\ msgs' = Socket!Send(Socket!Recv(msgs, i), smsg)
    /\ UNCHANGED <<state, timer>>

RecvPong(n) ==
    /\ state[n] = "wait_pong"
    /\ ~TimedOut(timer[n])
    /\ Socket!RecvEn(n, 1 - n)
    /\ LET i == Socket!PeekRecv(n, 1 - n)
           msg == msgs[i]
       IN /\ msg.payload = "pong"
          /\ msgs' = Socket!Recv(msgs, i)
    /\ state' = [state EXCEPT ![n] = "ready"]
    /\ timer' = [timer EXCEPT ![n] = MaxTimer]
 
TimeoutPong(n) ==
    /\ state[n] = "wait_pong"
    /\ TimedOut(timer[n])
    /\ state' = [state EXCEPT ![n] = "ready"]
    /\ timer' = [timer EXCEPT ![n] = MaxTimer]
    /\ UNCHANGED msgs

DropPong(n) ==
    /\ state[n] # "wait_pong"
    /\ Socket!RecvEn(n, 1 - n)
    /\ LET i == Socket!PeekRecv(n, 1 - n)
           msg == msgs[i]
       IN /\ msg.payload = "pong"
          /\ msgs' = Socket!Recv(msgs, i)
    /\ UNCHANGED <<state, timer>>

Tick ==
    /\ \E n \in Node : Enabled(timer[n])
    /\ timer' = [n \in Node |-> TimerTick(timer[n])] 
    /\ UNCHANGED <<state, msgs>>

Next ==
    \/ \E n \in Node : Ping(n)
    \/ \E n \in Node : Pong(n)
    \/ \E n \in Node : RecvPong(n)
    \/ \E n \in Node : TimeoutPong(n)
    \/ \E n \in Node : DropPong(n)
    \/ Socket!Fail /\ UNCHANGED <<state, timer>>
    \/ Tick

vars == <<state, timer, msgs>>

Liveness ==
    /\ \E n \in Node :
        WF_vars(Ping(n) /\ Pong(n) /\ RecvPong(n) /\ TimeoutPong(n) /\ DropPong(n))
    /\ SF_vars(Tick)

Spec == Init /\ [][Next]_vars
====
