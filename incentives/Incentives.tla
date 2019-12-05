---- MODULE Incentives -----------------------------------------------------
EXTENDS Naturals, Sequences, Bags
(* Documentation *)
(* This specification deals with the handling of packets according to the incentive scheme *)

(* Implicit assumptions include reliable transport layer with no delay, the neighbour
a request is forwarded to is irrelevant, no peer can be impersonated (sources are cryptographically signed),
load is modelled as binary, fixed number of peers guaranteed to be honest *)
--------------------------------------------------------------------------------
VARIABLES trust, relaytable, b_in, q_out
vars == <<trust, relaytable, b_in, q_out>>

(* CONSTANT Peers, Resources, Priority, MaxTrust, LoadBound, OutBound, Type, rqst, rply, Packet *)
Peers == 0..1
Resources == 0..0
Priority == 0..1
MaxTrust == 2
MaxIn == <<1,1>>
LoadBound == 1
OutBound == 1
Type == {1,2}
rqst == 1
rply == 2
Packet == [src : Peers, dst : Peers, type : Type, pr : Priority, res : Resources]

(* TODO adapt this to sensible value *)
reduction == 3


Add(B,elt) == B (+) SetToBag({elt})
Rm(B,elt) == B (-) SetToBag({elt})
Min(x, y) == IF x >= y THEN y ELSE x
Max(x, y) == IF x >= y THEN x ELSE y
EffPriority(p,pkt) == Min(pkt.pr, trust[p,pkt.src])
Debit(p,pkt) == [trust EXCEPT ![p,pkt.src] = Min(@ - pkt.pr, 0) ]
Credit(p,pkt) == [trust EXCEPT ![p,pkt.src] = Max(@ + pkt.pr, MaxTrust) ]

TypeInv ==
    /\ \A <<p1,p2>> \in Peers \X Peers : /\ p1 # p2 => trust[p1,p2] \in 0..MaxTrust
                                         /\ p1 = p2 => trust[p1,p2] = MaxTrust + 1
    /\ \A p \in Peers : IsABag(relaytable[p])
    /\ \A <<p,t>> \in Peers \X Type : IsABag(b_in[p,t])
    /\ \A p \in Peers : \A elt \in BagToSet(b_in[p,rqst]) :
                                                (* elt \in Packet \X 0..MaxTrust ? *)
                                                            /\ elt[1] \in Packet
                                                            /\ elt[2] \in 0..MaxTrust
                                                            /\ Len(elt) = 2
    /\ q_out \in [Peers -> Seq(Packet)]

--------------------------------------------------------------------------------

Init ==
    /\ relaytable = [peer \in Peers |-> EmptyBag]
    /\ b_in = [<<peer, type>> \in Peers \X Type |-> EmptyBag]
    /\ q_out = [peer \in Peers |-> << >>]
    /\ trust = [<<p1,p2>> \in Peers \X Peers |-> IF p1 = p2 THEN MaxTrust + 1 ELSE 0]

(* Don't charge trust when load low *)
RcvRqstLowLoad(rcv,pkt) ==
    /\ BagCardinality(b_in[rcv,rqst]) < LoadBound
    /\ b_in' = [b_in EXCEPT ![rcv,rqst] = Add(b_in[rcv,rqst],<<pkt,0>>)]
    /\ UNCHANGED <<relaytable, trust>>

(* If enough packets in buffer start charging trust *)
RcvRqstHighLoad(rcv,pkt) ==
    /\ BagCardinality(b_in[rcv,rqst]) >= LoadBound
    /\ BagCardinality(b_in[rcv,rqst]) < MaxIn[rqst]
    /\ b_in' = [b_in EXCEPT ![rcv,rqst] = Add(b_in[rcv,rqst], <<pkt, EffPriority(rcv,pkt)>>)]
    /\ trust' = [trust EXCEPT ![rcv,pkt.src] = @ - EffPriority(rcv,pkt)]
    /\ UNCHANGED <<relaytable>>

(* If max packets in buffer start exchanging them, adapting trust accordingly *)
RcvRqstLimit(rcv,pkt) ==
    /\ BagCardinality(b_in[rcv,rqst]) = MaxIn[rqst]
    /\ LET AllPkts == BagToSet(Add(b_in[rcv,rqst],<<pkt, EffPriority(rcv,pkt)>>))
           min == CHOOSE min \in AllPkts : \A elt \in AllPkts : elt[2] >= min[2]
       IN /\ b_in' = [b_in EXCEPT ![rcv,rqst] = Rm(SetToBag(AllPkts),min)]
          /\ trust' = [trust EXCEPT ![rcv,min[1].src] = Max(@ + min[2],MaxTrust),
                                    ![rcv,pkt.src] = @ - EffPriority(rcv,pkt)]
    /\ UNCHANGED <<relaytable>>

(* If enough packets in buffer start charging trust *)
RcvRply(rcv,pkt) ==
    /\ BagCardinality(b_in[rcv,rply]) < MaxIn[rply]
    /\ b_in' = [b_in EXCEPT ![rcv,rply] = Add(b_in[rcv,rply], pkt)]
    /\ trust' = [trust EXCEPT ![rcv,pkt.src] = Max(0,@ - reduction)]
    /\ UNCHANGED <<relaytable>>

(* If max packets in buffer start exchanging them, adapting trust accordingly *)
RcvRplyLimit(rcv,pkt) ==
    /\ BagCardinality(b_in[rcv,rply]) = MaxIn[rply]
    /\ LET AllPkts == BagToSet(Add(b_in[rcv,rply],pkt))
           min == CHOOSE min \in AllPkts :
           \A elt \in AllPkts : trust[rcv,min.src] <= trust[rcv,pkt.src]
       IN /\ b_in' = [b_in EXCEPT ![rcv,rply] = Rm(SetToBag(AllPkts),min)]
          /\ trust' = [trust EXCEPT ![rcv,min.src] = Max(@ + reduction,MaxTrust),
                                    ![rcv,pkt.src] = Max(0,@ - reduction)]
    /\ UNCHANGED <<relaytable>>

Send(p) ==
    (* Send packet from peer p *)
    /\ q_out[p] # << >>
    /\ q_out' = [q_out EXCEPT ![p] = Tail(q_out[p])]
    (* Receive the packet at peer pkt.dst *)
    /\ LET pkt == Head(q_out[p])
           rcv == pkt.dst
          (* If type is a request, check priority and add accordingly to queue *)
       IN \/ /\ pkt.type = rqst
             /\ \/ RcvRqstLowLoad(rcv,pkt)
                \/ RcvRqstHighLoad(rcv,pkt)
                \/ RcvRqstLimit(rcv,pkt)
          (* If type is a reply, check priority of matching request and add accordingly to queue *)
          \/ /\ pkt.type = rply
             /\ \/ RcvRply(rcv,pkt)
                \/ RcvRplyLimit(rcv,pkt)

CreateReq ==
    /\ \E p \in Peers : \E pkt \in Packet : /\ pkt.src = p
                                            /\ pkt.dst # p
                                            /\ pkt.type = 1
                                            /\ q_out' = [q_out EXCEPT ![p] = Append(q_out[p],pkt)]
    /\ UNCHANGED <<b_in, trust, relaytable>>

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
