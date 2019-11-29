---- MODULE IncentivesR -----------------------------------------------------
EXTENDS Naturals, Sequences, Bags
(* Documentation *)
(* This specification deals with the handling of packets according to the incentive scheme *)

(* Implicit assumptions include reliable transport layer with no delay, the neighbour
a request is forwarded to is irrelevant, no peer can be impersonated (sources are cryptographically signed),
load is modelled as binary, fixed number of peers guaranteed to be honest *)
--------------------------------------------------------------------------------
(* CONSTANT Peers *)
VARIABLES trust, relaytable, b_in0, q_out
vars == <<trust, relaytable, b_in0, q_out>>

(* For the moment these are fixed *)
Peers == 0..1
Resources == 0..0
Priority == 0..1
MaxTrust == 2
MaxIn == <<2,2>>
LoadBound == <<1,1>>
OutBound == 1
Packet == [src : Peers, dst : Peers, type : {1,2}, pr : Priority, res : Resources]

Add(B,elt) == B (+) SetToBag({elt})
Min(x, y) == IF x >= y THEN y ELSE x
(* Min(x) == x *)
Max(x, y) == IF x >= y THEN x ELSE y
EffPriority(p,paket) == Min(paket.pr, trust[p,paket.src])
Debit(p,paket) == [trust EXCEPT ![p,paket.src] = Min(@ - paket.pr, 0) ]
Credit(p,paket) == [trust EXCEPT ![p,paket.src] = Max(@ + paket.pr, MaxTrust) ]

TypeInv ==
    (* /\ trust \in [Peers \X Peers -> 0..MaxTrust+1] *)
    /\ \A <<p1,p2>> \in Peers \X Peers : /\ p1 # p2 => trust[p1,p2] \in 0..MaxTrust
                                         /\ p1 = p2 => trust[p1,p2] = MaxTrust + 1
    /\ \A p \in Peers : IsABag(relaytable[p])
    /\ \A p \in Peers : IsABag(b_in0[p])
    (* /\ \A p \in Peers : BagCardinality(b_in[p]) < 0 *)
    (* /\ b_in \in [Peers -> Seq(Packet)] *)
    /\ q_out \in [Peers -> Seq(Packet)]

--------------------------------------------------------------------------------

Init ==
    (* /\ TypeInv *)
    /\ relaytable = [peer \in Peers |-> EmptyBag]
    /\ b_in0 = [peer \in Peers |-> EmptyBag]
    /\ q_out = [peer \in Peers |-> << >>]
    /\ trust = [<<p1,p2>> \in Peers \X Peers |-> IF p1 = p2 THEN MaxTrust + 1 ELSE 0]

Send(p) ==
    (* Send packet from peer p *)
    /\ q_out[p] # << >>
    /\ q_out' = [q_out EXCEPT ![p] = Tail(q_out[p])]
    (* Receive the packet at peer pkt.dst *)
    /\ LET pkt == Head(q_out[p])
           receiver == pkt.dst
       IN /\ pkt.type = 1 (* IF type is a request, check priority and add accordingly to queue *)
          /\ \/ /\ BagCardinality(b_in0[receiver]) < LoadBound[1]
                /\ b_in0' = [b_in0 EXCEPT ![receiver] = Add(b_in0[receiver],<<pkt,0>>)]
                /\ UNCHANGED <<relaytable, trust>>
                (* If enough packets in buffer start charging trust *)
             \/ /\ BagCardinality(b_in0[receiver]) >= LoadBound[1]
                /\ BagCardinality(b_in0[receiver]) < MaxIn[1]
                /\ b_in0' = [b_in0 EXCEPT ![receiver] = Add(b_in0[receiver],
                                                             <<pkt, EffPriority(receiver,pkt)>>)]
                /\ trust' = [trust EXCEPT ![receiver,p] = @ - EffPriority(receiver,pkt)]
                /\ UNCHANGED <<relaytable>>
             (* If max packets in buffer start exchanging them, adapting trust accordingly *)
             \/ /\ BagCardinality(b_in0[receiver]) = MaxIn[1]
                /\ LET AllPkts == BagToSet(b_in0[receiver] (+) SetToBag({<<pkt, EffPriority(receiver,pkt)>>}))
                       min == CHOOSE min \in AllPkts : \A elt \in AllPkts : elt[2] >= min[2]
                   IN /\ b_in0' = [b_in0 EXCEPT ![receiver] = SetToBag(AllPkts) (-) SetToBag({min})]
                      /\ trust' = [trust EXCEPT ![receiver,min[1].src] = Max(@ + min[2],MaxTrust),
                                             ![receiver,pkt.src] = @ - EffPriority(receiver,pkt)]
                /\ UNCHANGED <<relaytable>>

CreateReq ==
    /\ \E p \in Peers : \E pkt \in Packet : /\ pkt.src = p
                                            /\ pkt.dst # p
                                            /\ pkt.type = 0
                                            /\ q_out' = [q_out EXCEPT ![p] = Append(q_out[p],pkt)]
                                            (* /\ Print(BagToSet(b_in[p]),TRUE) *)
    /\ UNCHANGED <<b_in0, trust, relaytable>>

SendRcv ==
    \E p \in Peers : Send(p)

(* Process(p) == *)
(*     /\ b_in[p] # EmptyBag *)
(*     /\ LET pkt == CHOOSE pkt1 \in BagToSet(b_in[p]) : \A pkt2 \in BagToSet(b_in[p]) : pkt1.p >= pkt2.p *)
(*        IN pkt.p = 1 *)

Next ==
    \/ CreateReq
    \/ SendRcv

Spec == Init /\ [][Next]_vars
================================================================================
THEOREM Spec => []TypeInv
================================================================================
