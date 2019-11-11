---- MODULE Incentives -----------------------------------------------------
EXTENDS Naturals, Sequences
(* Documentation *)
(* This specification deals with the handling of packets according to the incentive scheme *)

(* Implicit assumptions include reliable transport layer WITH no delay, the neighbour
a request is forwarded to is irrelevant, no peer can be impersonated (sources are cryptographically signed),
load is modelled as binary, fixed number of peers guaranteed to be honest *)
--------------------------------------------------------------------------------
CONSTANT Peers, Honest, LoadBound, Resource, TrustBound, Self
VARIABLES q, load, out, trust, None
ASSUME /\ LoadBound \in Nat
       /\ LoadBound > 0

ASSUME /\ Honest \subseteq Peers

(* Maybe remove later to model adversary *)
ASSUME /\ Self \in Honest

(* This queue contains incoming packets from other peers with given priority *)
Priority == Nat
Packet == [src : Peers, type : {0, 1}, res : Resource, p : Priority]
Request(pkt) == pkt.type = 0
Reply(pkt) == pkt.type = 1
Sorted(queue) == \A << index1, index2 >> \in {1..Len(queue)} \X {1..Len(queue)} : ((index1 <= index2) => (queue.p[index1] >= queue.p[index2]))

(* the buffer of the incoming requests to be serviced, sorted BY effective priority *)
Type_q == /\ q \in Seq(Packet)
          /\ Sorted(q)
(* does the load of the network at our peer exceed a chosen threshold? *)
Type_load == load \in {0,1}
(* an outgoing, sent request *)
Type_out == out \in Packet \cup {None}
(* trust of peer self IN neighbours *)
Type_trust == /\ trust \in [Peers -> Nat]
              /\ \A peer \in Peers : trust[peer] <= Trustbound
(* neighbours trust IN peer self *)
(* TODO *)

TypeInvariant == /\ Type_q
                 /\ Type_load
                 /\ Type_out
                 /\ Type_trust

--------------------------------------------------------------------------------

Init_q == <<>>
Init_load == 0
Init_out == None
Init_trust == \A peer \in Peers : trust[peer] = 0

Init == /\ TypeInvariant
        /\ Init_q
        /\ Init_load
        /\ Init_out
        /\ Init_trust

MIN(x, y) == IF x >= y THEN y ELSE x
MAX(x, y) == IF x >= y THEN x ELSE y
EFFTRUST(pkt) == [pkt EXCEPT !.p = MIN(pkt.p, trust[pkt.src])]
LOAD(qs) == IF Len(qs) >= LoadBound THEN 1 ELSE 0
DEBIT(pkt) == [trust EXCEPT ![pkt.src] = MIN(@ - EFFTRUST(pkt), 0) ]
CREDIT(pkt) == [trust EXCEPT ![pkt.src] = MAX(@ + pkt.p, Trustbound) ]

(* if the load is zero, anonymous relay operation *)
(* Append == /\ *)

Relay == /\ q /= << >>
         /\ out = None
         /\ \E << peer, max >> \in Peers \ {Self} \X q : \A pkt \in q : /\ pkt.p <= max.p
                                                                        /\ q' = q \ {max}
         /\ load' = LOAD(q')
         /\ trust' = DEBIT(Head(q))

Rcv_load == /\ load = 1
            /\ \E << received, less >> \in Packet \X q :  /\ less.p < MIN(received.p, trust[received.src])
                                                          /\ q' = Append(q \ {less}, EFFTRUST(received))

Rcv_noload == /\ load = 0
              /\ \E received \in Packet : q' = Append(q, received)

Rcv == Rcv_load \/ Rcv_noload

Next == Rcv (* \/ \E d \in Nat : Send(d) *)

SPEC == Init /\ [][Next]_<< q, load, out, trust >>
================================================================================
THEOREM SPEC => []TypeInvariant
================================================================================
