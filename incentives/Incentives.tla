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

CONSTANT Peers, Resources, Priority, MaxTrust, LoadBound, OutBound
(* Peers == 0..1 *)
(* Resources == 0..0 *)
(* Priority == Nat *)
(* MaxTrust == 1 *)
MaxIn == <<1,1>>
(* LoadBound == 1 *)
(* OutBound == 1 *)
Type == {1,2}
rqst == 1
rply == 2
Request == [src : Peers, dst : Peers, pr : Priority, res : Resources]
Reply == [src : Peers, dst : Peers, res : Resources]
Packet == Request \cup Reply

(* TODO adapt this to sensible value *)
c == 3


Add(B,elt) == B (+) SetToBag({elt})
Rm(B,elt) == B (-) SetToBag({elt})
Swap(B,rm,add) == Add(Rm(B,rm),add)
Min(x, y) == IF x >= y THEN y ELSE x
Max(x, y) == IF x >= y THEN x ELSE y
EffPriority(p,pkt) == Min(pkt.pr, trust[p,pkt.src])
Debit(p,pkt,type) == [trust EXCEPT ![p,pkt.src] = Max(0, @ - IF type = rqst THEN pkt.pr ELSE c)]
Credit(p,pkt,type) == [trust EXCEPT ![p,pkt.src] = Min(@ + pkt.pr, MaxTrust) ]

TypeInv ==
    /\ \A <<p1,p2>> \in Peers \X Peers : /\ p1 # p2 => trust[p1,p2] \in 0..MaxTrust
                                         /\ p1 = p2 => trust[p1,p2] = MaxTrust + 1
    /\ \A p \in Peers : IsABag(relay[p])
    /\ \A p \in Peers : \A elt \in BagToSet(relay[p]) : elt \in Request
    /\ \A <<p,t>> \in Peers \X Type : IsABag(in[p,t])
    /\ \A p \in Peers : \A elt \in BagToSet(in[p,rqst]) :
                                                (* elt \in Packet \X 0..MaxTrust ? *)
                                                            /\ elt[1] \in Request
                                                            /\ elt[2] \in 0..MaxTrust
                                                            /\ Len(elt) = 2
    /\ \A p \in Peers : \A elt \in BagToSet(in[p,rply]) : elt \in Reply
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
    (* /\ trust' = [trust EXCEPT ![rcv,pkt.src] = @ - EffPriority(rcv,pkt)] *)
    /\ trust' = Debit(rcv,pkt,rqst)
    /\ UNCHANGED <<own, relay, n>>

(* If max packets in buffer start exchanging them, adapting trust accordingly *)
(* assumes packet addressed to receiver *)
RcvRqstLimit(rcv,pkt) ==
    /\ BagCardinality(in[rcv,rqst]) = MaxIn[rqst]
    /\ \E min \in BagToSet(in[rcv,rqst]) : min[2] < EffPriority(rcv,pkt)
    /\ LET min == CHOOSE min \in BagToSet(in[rcv,rqst]) : min[2] < EffPriority(rcv,pkt)
       IN /\ in' = [in EXCEPT ![rcv,rqst] = Swap(@,min,<<pkt,EffPriority(rcv,pkt)>>)]
          /\ trust' = [Debit(rcv,pkt,rqst) EXCEPT ![rcv,min[1].src] = Min(@ + min[2],MaxTrust)]
    /\ UNCHANGED <<own, relay, n>>

(* If enough packets in buffer start charging trust *)
(* assumes packet addressed to receiver *)
RcvRply(rcv,pkt) ==
    \/ /\ CopiesIn(pkt.res,n[rcv]) # 0
       /\ BagCardinality(in[rcv,rply]) < MaxIn[rply]
       (* /\ pkt.res \in BagToSet(n[rcv]) *)
       /\ in' = [in EXCEPT ![rcv,rply] = Add(in[rcv,rply], pkt)]
       /\ trust' = Debit(rcv,pkt,rply)
       /\ n' = [n EXCEPT ![rcv] = Rm(@,pkt.res)]
       /\ UNCHANGED <<own, relay>>
    \/ /\ CopiesIn(pkt.res,n[rcv]) = 0
       /\ UNCHANGED <<own, relay, n, trust, in>>

(* If max packets in buffer start exchanging them, adapting trust accordingly *)
(* assumes packet addressed to receiver *)
RcvRplyLimit(rcv,pkt) ==
    \/ /\ CopiesIn(pkt.res,n[rcv]) # 0
       /\ BagCardinality(in[rcv,rply]) = MaxIn[rply]
       /\ pkt.res \in BagToSet(n[rcv])
       /\ \E min \in BagToSet(in[rcv,rply]) : trust[rcv,min.src] < trust[rcv,pkt.src]
       /\ LET min == CHOOSE min \in BagToSet(in[rcv,rply]) : trust[rcv,min.src] < trust[rcv,pkt.src]
          IN /\ in' = [in EXCEPT ![rcv,rply] = Swap(@,min,pkt)]
             /\ trust' = [Debit(rcv,pkt,rply) EXCEPT ![rcv,min.src] = Min(@ + c,MaxTrust)]
             /\ n' = [n EXCEPT ![rcv] = Swap(@,min.res,pkt.res)]
       /\ UNCHANGED <<own, relay>>
    \/ /\ CopiesIn(pkt.res,n[rcv]) = 0
       /\ UNCHANGED <<own, relay, n, trust, in>>

(* Send packet from peer p *)
Send(p,pkt) ==
    /\ out[p] # << >>
    /\ out' = [out EXCEPT ![p] = Tail(out[p])]
    /\ pkt = Head(out[p])
    /\ UNCHANGED <<own, relay>>

(* Receive the packet at p *)
Rcv(p,pkt) ==
    (* if addressed to receiving peer, proceed normally *)
    \/ /\ pkt.dst = p
       /\ \/ /\ pkt \in Request
             /\ \/ RcvRqstLowLoad(p,pkt)
                \/ RcvRqstHighLoad(p,pkt)
                \/ RcvRqstLimit(p,pkt)
          \/ /\ pkt \in Reply
             /\ \/ RcvRply(p,pkt)
                \/ RcvRplyLimit(p,pkt)
    (* TODO discard if not addressed to receiving peer *)
    \/ /\ pkt.dst # p
       /\ trust' = [trust EXCEPT ![p,pkt.src] = Max(0,@ - c)]
       /\ UNCHANGED <<n, own, in, relay>>

CreateRqst(p,pkt) ==
    /\ pkt \in Request
    /\ pkt.src = p
    /\ pkt.dst # p
    /\ out' = [out EXCEPT ![p] = Append(out[p],pkt)]
    /\ own' = [own EXCEPT ![p] = Add(@,[res |-> pkt.res, pr |-> pkt.pr])]
    /\ n' = [n EXCEPT ![p] = Add(@,pkt.res)]
    /\ UNCHANGED <<in, trust, relay>>

(* relay a request *)
Relay(p,nxt) ==
    /\ in[p,rqst] # EmptyBag
    /\ LET In == BagToSet(in[p,rqst])
           max == CHOOSE max \in In : \A elt \in In : max[2] >= elt[2]
           pkt == max[1]
       IN /\ relay' = [relay EXCEPT ![p] = Add(@,[pkt EXCEPT !.dst = p, !.pr = max[2]])]
          /\ out' = [out EXCEPT ![p] = Append(@,[src |-> p, dst |-> nxt, pr |-> 0, res |-> pkt.res])]
          /\ n' = [n EXCEPT ![p] = Add(@,max[1].res)]
          /\ in' = [in EXCEPT ![p,rqst] = Rm(@,pkt)]
          /\ UNCHANGED <<own, trust>>

(* reply to a request *)
Rply(p) ==
    /\ in[p,rqst] # EmptyBag
    /\ LET In == BagToSet(in[p,rqst])
           (* choose packet with maximal priority *)
           max == CHOOSE max \in In : \A elt \in In : max[2] >= elt[2]
           pkt == max[1]
           answer == [src |-> p, dst |-> pkt.src, res |-> pkt.res]
       IN /\ out' = [out EXCEPT ![p] = Append(@,answer)]
          (* /\ Print(pkt,TRUE) *)
          /\ in' = [in EXCEPT ![p,rqst] = Rm(@,max)]
          /\ UNCHANGED <<own, trust, relay, n>>

PrcRqst(p) ==
    \/ Rply(p)
    (* next peer cannot be the same one that processed the request *)
    \/ \E nxt \in Peers \ {p} : Relay(p,nxt)

MatchesWithIn(p,bag) ==
    {r \in BagToSet(bag) :
    \E i \in BagToSet(in[p,rply]) : (* /\ i.src = r.src *) /\ i.res = r.res}

ConsumeRply(p) ==
    /\ MatchesWithIn(p,own[p]) # {}
    /\ LET max == CHOOSE max \in MatchesWithIn(p,own[p]) :
           \A elt \in MatchesWithIn(p,own[p]) : max.pr >= elt.pr
           pkt == CHOOSE pkt \in BagToSet(in[p,rply]) : pkt.res = max.res
       IN /\ trust' = [trust EXCEPT ![p,pkt.src] = Min(@ + c + max.pr,MaxTrust)]
          /\ in' = [in EXCEPT ![p,rply] = Rm(@,pkt)]
          /\ own' = [own EXCEPT ![p] = Rm(@,max)]
          /\ UNCHANGED <<out, relay, n>>

FrwdRply(p) ==
    (* IN not empty, pick response to packet with maximum priority *)
    /\ in[p,rply] # EmptyBag
    /\ \E max \in MatchesWithIn(p,relay[p]) :
       \A elt \in MatchesWithIn(p,relay[p]) : max.pr >= elt.pr
    /\ LET max == CHOOSE max \in MatchesWithIn(p,relay[p]) :
                      \A elt \in MatchesWithIn(p,relay[p]) : max.pr >= elt.pr
           frwd == [max EXCEPT !.src = p, !.dst = max.src]
       IN /\ relay' = [relay EXCEPT ![p] = Rm(@,max)]
          /\ in' = [in EXCEPT ![p,rply] = Rm(@,max)]
          /\ out' = [out EXCEPT ![p] = Append(@,frwd)]
          /\ trust' = [trust EXCEPT ![p,max.src] = Min(@ + c,MaxTrust)]
    /\ UNCHANGED <<own,n>>

PrcRply(p) ==
    \/ ConsumeRply(p)
    \/ FrwdRply(p)
(*     \/ /\ *)
(*     /\ in[p,rply] # EmptyBag *)

Next ==
    \/ \E p \in Peers : PrcRqst(p)
    \/ \E p \in Peers : PrcRply(p)
    \/ \E p \in Peers : \E pkt \in Packet : CreateRqst(p,pkt)
    \/ \E src \in Peers :
       \E dst \in Peers \ {src} :
       \E pkt \in Packet : /\ Send(src,pkt)
                           /\ Rcv(dst,pkt)
    (* \/ /\ Print(out,TRUE) *)
    (*    /\ UNCHANGED vars *)

Fairness ==
    \A p \in Peers :
    \A pkt \in Packet :
    \A src \in Peers :
    \A dst \in Peers :
    /\ WF_vars(PrcRqst(p))
    /\ WF_vars(PrcRply(p))
    /\ WF_vars(Send(src,pkt) /\ Rcv(dst,pkt))
    /\ WF_vars(CreateRqst(p,pkt))
    /\ WF_vars(ConsumeRply(p))

Spec == Init /\ [][Next]_vars /\ Fairness
RcvEnabled == \A p \in Peers : \E pkt \in Reply : ENABLED Rcv(p,pkt)
SendRcvEnabled == \A p \in Peers : Len(out[p]) # 0 => \E pkt \in Packet : \E p2 \in Peers : ENABLED Send(p,pkt) /\ ENABLED Rcv(p2,pkt)
CreateEnabled == \A p \in Peers : \A pkt \in Request : pkt.src = p /\ pkt.dst # p => ENABLED CreateRqst(p,pkt)
(* Fail == \A p \in Peers : \A p2 \in Peers \ {p} : \E pkt \in Reply : /\ ENABLED Send(p,pkt) *)
(*                                                                     /\ ENABLED Rcv(p2,pkt) *)
================================================================================
THEOREM Spec => []TypeInv
================================================================================
