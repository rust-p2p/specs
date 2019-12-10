---- MODULE Incentives -----------------------------------------------------
EXTENDS Naturals, Sequences, Bags
(* Documentation *)
(* This specification deals with the handling of packets according to the incentive scheme *)

(* Implicit assumptions include reliable transport layer with no delay, the neighbour
a request is forwarded to is irrelevant, no peer can be impersonated (sources are cryptographically signed),
load is modelled as binary, fixed number of peers guaranteed to be honest *)
--------------------------------------------------------------------------------
VARIABLES own, trust, relay, in, out, n
vars == <<own, trust, relay, in, out, n>>

(* CONSTANT Peers, Resources, Priority, MaxTrust, LoadBound, OutBound, Type, rqst, rply, Packet *)
Peers == 0..1
Resources == 0..0
Priority == 0..0
MaxTrust == 1
MaxIn == <<1,1>>
LoadBound == 1
OutBound == 1
Type == {1,2}
rqst == 1
rply == 2
Packet == [src : Peers, dst : Peers, type : Type, pr : Priority, res : Resources]

(* TODO adapt this to sensible value *)
c == 3


Add(B,elt) == B (+) SetToBag({elt})
Rm(B,elt) == B (-) SetToBag({elt})
Min(x, y) == IF x >= y THEN y ELSE x
Max(x, y) == IF x >= y THEN x ELSE y
EffPriority(p,pkt) == Min(pkt.pr, trust[p,pkt.src])
Debit(p,pkt) == [trust EXCEPT ![p,pkt.src] = Max(@ - pkt.pr, 0) ]
Credit(p,pkt) == [trust EXCEPT ![p,pkt.src] = Min(@ + pkt.pr, MaxTrust) ]

TypeInv ==
    /\ \A <<p1,p2>> \in Peers \X Peers : /\ p1 # p2 => trust[p1,p2] \in 0..MaxTrust
                                         /\ p1 = p2 => trust[p1,p2] = MaxTrust + 1
    /\ \A p \in Peers : IsABag(relay[p])
    /\ \A p \in Peers : \A elt \in BagToSet(relay[p]) : elt \in Packet
    /\ \A <<p,t>> \in Peers \X Type : IsABag(in[p,t])
    /\ \A p \in Peers : \A elt \in BagToSet(in[p,rqst]) :
                                                (* elt \in Packet \X 0..MaxTrust ? *)
                                                            /\ elt[1] \in Packet
                                                            /\ elt[2] \in 0..MaxTrust
                                                            /\ Len(elt) = 2
    /\ \A p \in Peers : \A elt \in BagToSet(in[p,rply]) : elt \in Packet
    /\ out \in [Peers -> Seq(Packet)]
    /\ \A p \in Peers : IsABag(own[p])
    /\ \A p \in Peers : \A elt \in BagToSet(own[p]) : elt \in [res : Resources, pr : Priority]
    /\ \A p \in Peers : IsABag(n[p])
    /\ \A p \in Peers : \A elt \in BagToSet(n[p]) : elt \in Resources

--------------------------------------------------------------------------------

Init ==
    /\ relay = [peer \in Peers |-> EmptyBag]
    /\ in = [<<peer, type>> \in Peers \X Type |-> EmptyBag]
    /\ out = [peer \in Peers |-> << >>]
    /\ trust = [<<p1,p2>> \in Peers \X Peers |-> IF p1 = p2 THEN MaxTrust + 1 ELSE 0]
    /\ own = [peer \in Peers |-> EmptyBag]
    /\ n = [peer \in Peers |-> EmptyBag]

(* Don't charge trust when load low *)
(* assumes packet addressed to receiver *)
RcvRqstLowLoad(rcv,pkt) ==
    /\ BagCardinality(in[rcv,rqst]) < LoadBound
    /\ in' = [in EXCEPT ![rcv,rqst] = Add(in[rcv,rqst],<<pkt,0>>)]
    /\ UNCHANGED <<own, relay, trust, n>>

(* If enough packets in buffer start charging trust *)
(* assumes packet addressed to receiver *)
RcvRqstHighLoad(rcv,pkt) ==
    /\ BagCardinality(in[rcv,rqst]) >= LoadBound
    /\ BagCardinality(in[rcv,rqst]) < MaxIn[rqst]
    /\ in' = [in EXCEPT ![rcv,rqst] = Add(in[rcv,rqst], <<pkt, EffPriority(rcv,pkt)>>)]
    /\ trust' = [trust EXCEPT ![rcv,pkt.src] = @ - EffPriority(rcv,pkt)]
    /\ UNCHANGED <<own, relay, n>>

(* If max packets in buffer start exchanging them, adapting trust accordingly *)
(* assumes packet addressed to receiver *)
RcvRqstLimit(rcv,pkt) ==
    /\ BagCardinality(in[rcv,rqst]) = MaxIn[rqst]
    /\ LET AllPkts == BagToSet(Add(in[rcv,rqst],<<pkt, EffPriority(rcv,pkt)>>))
           min == CHOOSE min \in AllPkts : \A elt \in AllPkts : elt[2] >= min[2]
       IN /\ in' = [in EXCEPT ![rcv,rqst] = Rm(SetToBag(AllPkts),min)]
          /\ trust' = [trust EXCEPT ![rcv,min[1].src] = Min(@ + min[2],MaxTrust),
                                    ![rcv,pkt.src] = @ - EffPriority(rcv,pkt)]
    /\ UNCHANGED <<own, relay, n>>

(* If enough packets in buffer start charging trust *)
(* assumes packet addressed to receiver *)
RcvRply(rcv,pkt) ==
    /\ BagCardinality(in[rcv,rply]) < MaxIn[rply]
    /\ pkt.res \in BagToSet(n[rcv])
    /\ in' = [in EXCEPT ![rcv,rply] = Add(in[rcv,rply], pkt)]
    /\ trust' = [trust EXCEPT ![rcv,pkt.src] = Max(0,@ - c)]
    /\ n' = [n EXCEPT ![rcv] = Rm(@,pkt.res)]
    /\ UNCHANGED <<own, relay, n>>

(* If max packets in buffer start exchanging them, adapting trust accordingly *)
(* assumes packet addressed to receiver *)
RcvRplyLimit(rcv,pkt) ==
    /\ BagCardinality(in[rcv,rply]) = MaxIn[rply]
    /\ pkt.res \in BagToSet(n[rcv])
    /\ LET AllPkts == BagToSet(Add(in[rcv,rply],pkt))
           min == CHOOSE min \in AllPkts :
           \A elt \in AllPkts : trust[rcv,min.src] <= trust[rcv,pkt.src]
       IN /\ in' = [in EXCEPT ![rcv,rply] = Rm(SetToBag(AllPkts),min)]
          /\ trust' = [trust EXCEPT ![rcv,min.src] = Min(@ + c,MaxTrust),
                                    ![rcv,pkt.src] = Max(0,@ - c)]
          /\ n' = [n EXCEPT ![rcv] = Rm(Add(@,pkt.res),min.res)]
    /\ UNCHANGED <<own, relay>>

(* Send packet from peer p *)
Send(p,pkt) ==
    /\ out[p] # << >>
    /\ out' = [out EXCEPT ![p] = Tail(out[p])]
    /\ pkt = Head(out[p])
    /\ UNCHANGED <<own, relay, n>>

(* Receive the packet at p *)
Rcv(p,pkt) ==
    (* if addressed to receiving peer, proceed normally *)
    \/ /\ pkt.dst = p
       (* If type is a request, check priority and add accordingly to queue *)
       /\ \/ /\ pkt.type = rqst
             /\ \/ RcvRqstLowLoad(p,pkt)
                \/ RcvRqstHighLoad(p,pkt)
                \/ RcvRqstLimit(p,pkt)
          (* If type is a reply, check that matching request exists and add accordingly to queue *)
          \/ /\ pkt.type = rply
             /\ \E match \in BagToSet(relay[p]) : match.res = pkt.res
             /\ \/ RcvRply(p,pkt)
                \/ RcvRplyLimit(p,pkt)
    (* discard if not addressed to receiving peer *)
    \/ /\ pkt.dst # p
       /\ trust' = [trust EXCEPT ![p,pkt.src] = Max(0,@ - c)]
       /\ UNCHANGED <<n, own, in, relay>>

CreateReq(p,pkt) ==
    /\ pkt.src = p
    /\ pkt.dst # p
    /\ pkt.type = 1
    /\ out' = [out EXCEPT ![p] = Append(out[p],pkt)]
    /\ own' = [own EXCEPT ![p] = Add(@,[res |-> pkt.res, pr |-> pkt.pr])]
    /\ UNCHANGED <<in, trust, relay, n>>

(* relay a request *)
Relay(p,nxt) ==
    /\ in[p,rqst] # EmptyBag
    /\ LET In == BagToSet(in[p,rqst])
           max == CHOOSE max \in In : \A elt \in In : max[2] >= elt[2]
           pkt == max[1]
       IN /\ relay' = [relay EXCEPT ![p] = Add(@,[pkt EXCEPT !.dst = p, !.pr = max[2]])]
          /\ out' = [out EXCEPT ![p] = Append(@,[src |-> p, dst |-> nxt, type |-> rqst, pr |-> 0, res |-> pkt.res])]
          /\ n' = [n EXCEPT ![p] = Add(@,max[1].res)]
          /\ UNCHANGED <<own, trust, in>>

(* reply to a request *)
Rply(p) ==
    /\ in[p,rqst] # EmptyBag
    /\ LET In == BagToSet(in[p,rqst])
           (* choose packet with maximal priority *)
           max == CHOOSE max \in In : \A elt \in In : max[2] >= elt[2]
           pkt == max[1]
           answer == [src |-> p, dst |-> pkt.src, type |-> rply, pr |-> 0, res |-> pkt.res]
       IN /\ out' = [out EXCEPT ![p] = Append(@,answer)]
          /\ Print(pkt,TRUE)
          (* /\ in' = [in EXCEPT ![p,rqst] = Rm(@,pkt)] *)
          /\ UNCHANGED <<own, trust, relay, n>>

PrcRqst(p) ==
    \/ Rply(p)
    (* next peer cannot be the same one that processed the request *)
    \/ \E nxt \in Peers \ {p} : Relay(p,nxt)

ConsumeRply(p) ==
    (* pick reply to maximum priority request *)
    /\ own[p] # EmptyBag
    /\ \E toSelf \in BagToSet(own[p]) :
       \E pkt \in BagToSet(in[p,rply]) :
       \A elt \in BagToSet(own[p]) : /\ pkt.res = toSelf.res
                                     /\ toSelf.pr >= elt.pr
    /\ LET toSelf == CHOOSE toSelf \in BagToSet(own[p]) :
                     \E pkt \in BagToSet(in[p,rply]) : pkt.res = toSelf.res
           pkt == CHOOSE pkt \in BagToSet(in[p,rply]) : pkt.res = toSelf.res
       IN /\ trust' = [trust EXCEPT ![p,pkt.src] = Min(@ + c + toSelf.pr,MaxTrust)]
          /\ in' = [in EXCEPT ![p,rply] = Rm(@,pkt)]
          /\ own' = [own EXCEPT ![p] = Rm(@,toSelf)]
          /\ UNCHANGED <<out, relay, n>>

haveMatch(p) ==
    {r \in BagToSet(relay[p]) :
          \E i \in BagToSet(in[p,rply]) :
          /\ i.src = r.src
          /\ i.res = r.res}

FrwdRply(p) ==
    (* IN not empty, pick response to packet with maximum priority *)
    (* TODO increase trust IN peer providing answer *)
    (* TODO  *)
    /\ in[p,rply] # EmptyBag
    /\ \E max \in haveMatch(p) :
       \A elt \in haveMatch(p) : max.pr >= elt.pr
    /\ LET max == CHOOSE max \in haveMatch(p) :
                      \A elt \in haveMatch(p) : max.pr >= elt.pr
           frwd == [max EXCEPT !.src = p, !.dst = max.src]
       IN /\ relay' = [relay EXCEPT ![p] = Rm(@,max)]
          /\ in' = [in EXCEPT ![p,rply] = Rm(@,max)]
          /\ out' = [out EXCEPT ![p] = Append(@,frwd)]
          /\ trust' = [trust EXCEPT ![p,max.src] = Min(@ + c,MaxTrust)]
    /\ UNCHANGED own

PrcRply(p) ==
    \/ ConsumeRply(p)
    \/ FrwdRply(p)
(*     \/ /\ *)
(*     /\ in[p,rply] # EmptyBag *)

Next ==
    \/ \E p \in Peers : PrcRqst(p)
    \/ \E p \in Peers : PrcRply(p)
    \/ \E p \in Peers : \E pkt \in Packet : CreateReq(p,pkt)
    \/ \E src \in Peers :
       \E dst \in Peers \ {src} :
       \E pkt \in Packet : /\ Send(src,pkt)
                           /\ Rcv(dst,pkt)


Spec == Init /\ [][Next]_vars
================================================================================
THEOREM Spec => []TypeInv
================================================================================
