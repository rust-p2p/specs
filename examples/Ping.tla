---- MODULE Ping ----
EXTENDS BoundedTimer, Naturals, Sequences, Socket

VARIABLES state, timer

State == { "ready", "wait_pong" }

Init ==
    /\ SocketInit
    /\ state = [n \in Node |-> "ready"]
    /\ timer = [n \in Node |-> MaxTimer]

TypeInv ==
    /\ SocketTypeInv({"ping", "pong"})
    /\ state \in [Node -> State]
    /\ timer \in [Node -> Timer]

Ping(n) ==
    /\ state[n] = "ready"
    /\ msgs' = Send(msgs, Msg(n, 1 - n, "ping"))
    /\ state' = [state EXCEPT ![n] = "wait_pong"]
    /\ timer' = [timer EXCEPT ![n] = 1]

Pong(n) ==
    /\ RecvEn(n, 1 - n)
    /\ LET rmsg == PeekRecv(n, 1 - n)
           smsg == Msg(n, 1 - n, "pong")
       IN /\ rmsg.payload = "ping"
          /\ msgs' = Send(Recv(msgs, rmsg), smsg)
    /\ UNCHANGED <<state, timer>>

RecvPong(n) ==
    /\ state[n] = "wait_pong"
    /\ ~TimedOut(timer[n])
    /\ RecvEn(n, 1 - n)
    /\ LET msg == PeekRecv(n, 1 - n)
       IN /\ msg.payload = "pong"
          /\ msgs' = Recv(msgs, msg)
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
    /\ RecvEn(n, 1 - n)
    /\ LET msg == PeekRecv(n, 1 - n)
       IN /\ msg.payload = "pong"
          /\ msgs' = Recv(msgs, msg)
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
    \/ Fail /\ UNCHANGED <<state, timer>>
    \/ Tick

vars == <<state, timer, msgs>>

Liveness ==
    /\ \E n \in Node :
        WF_vars(Ping(n) /\ Pong(n) /\ RecvPong(n) /\ TimeoutPong(n) /\ DropPong(n))
    /\ SF_vars(Tick)

Spec == Init /\ [][Next]_vars
====
