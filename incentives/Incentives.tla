---- MODULE Incentives -----------------------------------------------------
EXTENDS Naturals, Sequences, Bags
(* Documentation *)
(* This specification deals with the handling of packets according to the incentive scheme *)

(* Implicit assumptions include reliable transport layer with no delay, the neighbour
a request is forwarded to is irrelevant, no peer can be impersonated (sources are cryptographically signed),
load is modelled as binary, fixed number of peers guaranteed to be honest *)
--------------------------------------------------------------------------------
VARIABLES own, trust, relay, in, out
vars == <<own, trust, relay, in, out>>

CONSTANT P, Honest, Byzantine, Resources, Priority, MaxTrust, LoadBound, OutBound
(* Priority == Nat *)
(* MaxTrust == 1 *)
Peers == Honest \cup Byzantine
MaxIn == <<1,1>>
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

(* without loss of generality it suffices to check invariants for one honest peer *)
(* P == CHOOSE p \in Honest *)

TypeInv ==
    /\ \A p \in Peers : /\ P # p => trust[P,p] \in 0..MaxTrust
                        /\ P = p => trust[P,p] = MaxTrust + 1
    /\ IsABag(relay[P])
    /\ \A elt \in BagToSet(relay[P]) : elt \in Request
    /\ \A t \in Type : IsABag(in[P,t])
    /\ \A elt \in BagToSet(in[P,rqst]) :
                                                (* elt \in Packet \X 0..MaxTrust ? *)
                                                            /\ elt[1] \in Request
                                                            /\ elt[2] \in 0..MaxTrust
                                                            /\ Len(elt) = 2
    /\ \A elt \in BagToSet(in[P,rply]) : elt \in Reply
    /\ out \in [Peers -> Seq(Packet)]
    /\ IsABag(own[P])
    /\ \A elt \in BagToSet(own[P]) : elt \in [res : Resources, pr : Priority]

--------------------------------------------------------------------------------

Init ==
    /\ relay = [peer \in Honest |-> EmptyBag]
    /\ in = [<<peer, type>> \in Honest \X Type |-> EmptyBag]
    /\ out = [peer \in Peers |-> << >>]
    /\ trust = [<<p1,p2>> \in Honest \X Peers |-> IF p1 = p2 THEN MaxTrust + 1 ELSE 0]
    /\ own = [peer \in Honest |-> EmptyBag]

(* Don't charge trust when load low *)
(* assumes packet addressed to receiver *)
RcvRqstLowLoad(rcv,pkt) ==
    /\ BagCardinality(in[rcv,rqst]) < LoadBound
    /\ in' = [in EXCEPT ![rcv,rqst] = Add(in[rcv,rqst],<<pkt,0>>)]
    /\ UNCHANGED <<own, relay, trust>>

(* If enough packets in buffer start charging trust *)
(* assumes packet addressed to receiver *)
RcvRqstHighLoad(rcv,pkt) ==
    /\ BagCardinality(in[rcv,rqst]) >= LoadBound
    /\ BagCardinality(in[rcv,rqst]) < MaxIn[rqst]
    /\ in' = [in EXCEPT ![rcv,rqst] = Add(in[rcv,rqst], <<pkt, EffPriority(rcv,pkt)>>)]
    /\ trust' = Debit(rcv,pkt,rqst)
    /\ UNCHANGED <<own, relay>>

(* If max packets in buffer start exchanging them, adapting trust accordingly *)
(* assumes packet addressed to receiver *)
RcvRqstLimit(rcv,pkt) ==
    /\ BagCardinality(in[rcv,rqst]) = MaxIn[rqst]
    /\ \E min \in BagToSet(in[rcv,rqst]) : min[2] < EffPriority(rcv,pkt)
    /\ LET min == CHOOSE min \in BagToSet(in[rcv,rqst]) : min[2] < EffPriority(rcv,pkt)
       IN /\ in' = [in EXCEPT ![rcv,rqst] = Swap(@,min,<<pkt,EffPriority(rcv,pkt)>>)]
          /\ trust' = [Debit(rcv,pkt,rqst) EXCEPT ![rcv,min[1].src] = Min(@ + min[2],MaxTrust)]
    /\ UNCHANGED <<own, relay>>

(* If enough packets in buffer start charging trust *)
(* assumes packet addressed to receiver *)
RcvRply(rcv,pkt) ==
    LET Eq(x) == x.res = pkt.res
        NrMatch(B) == BagCardinality(BagOfAll(Eq,B))
    IN
    \/ /\ NrMatch(own[rcv]) + NrMatch(relay[rcv]) > NrMatch(in[rcv,rply])
       /\ BagCardinality(in[rcv,rply]) < MaxIn[rply]
       /\ in' = [in EXCEPT ![rcv,rply] = Add(in[rcv,rply], pkt)]
       /\ trust' = Debit(rcv,pkt,rply)
       /\ UNCHANGED <<own, relay>>
    \/ /\ NrMatch(own[rcv]) + NrMatch(relay[rcv]) <= NrMatch(in[rcv,rply])
       /\ UNCHANGED <<own, relay, trust, in>>

(* If max packets in buffer start exchanging them, adapting trust accordingly *)
(* assumes packet addressed to receiver *)
RcvRplyLimit(rcv,pkt) ==
    LET Eq(x) == x.res = pkt.res
        NrMatch(B) == BagCardinality(BagOfAll(Eq,B))
    IN
    \/ /\ NrMatch(own[rcv]) + NrMatch(relay[rcv]) > NrMatch(in[rcv,rply])
       /\ BagCardinality(in[rcv,rply]) = MaxIn[rply]
       /\ \E min \in BagToSet(in[rcv,rply]) : trust[rcv,min.src] < trust[rcv,pkt.src]
       /\ LET min == CHOOSE min \in BagToSet(in[rcv,rply]) : trust[rcv,min.src] < trust[rcv,pkt.src]
          IN /\ in' = [in EXCEPT ![rcv,rply] = Swap(@,min,pkt)]
             /\ trust' = [Debit(rcv,pkt,rply) EXCEPT ![rcv,min.src] = Min(@ + c,MaxTrust)]
       /\ UNCHANGED <<own, relay>>
    \/ /\ NrMatch(own[rcv]) + NrMatch(relay[rcv]) <= NrMatch(in[rcv,rply])
       /\ UNCHANGED <<own, relay, trust, in>>

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
       /\ UNCHANGED <<trust, own, in, relay>>

CreateRqst(p,pkt) ==
    /\ pkt \in Request
    /\ pkt.src = p
    /\ pkt.dst # p
    /\ out' = [out EXCEPT ![p] = Append(out[p],pkt)]
    /\ own' = [own EXCEPT ![p] = Add(@,[res |-> pkt.res, pr |-> pkt.pr])]
    /\ UNCHANGED <<in, trust, relay>>

(* relay a request *)
Relay(p,nxt) ==
    /\ in[p,rqst] # EmptyBag
    /\ LET In == BagToSet(in[p,rqst])
           max == CHOOSE max \in In : \A elt \in In : max[2] >= elt[2]
           pkt == max[1]
       IN /\ relay' = [relay EXCEPT ![p] = Add(@,[pkt EXCEPT !.dst = p, !.pr = max[2]])]
          /\ out' = [out EXCEPT ![p] = Append(@,[src |-> p, dst |-> nxt, pr |-> 0, res |-> pkt.res])]
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
          /\ in' = [in EXCEPT ![p,rqst] = Rm(@,max)]
          /\ UNCHANGED <<own, trust, relay>>

PrcRqst(p) ==
    \/ Rply(p)
    (* next peer cannot be the same one that processed the request *)
    \/ \E nxt \in Peers \ {p} : Relay(p,nxt)

MatchesWithIn(p,bag) ==
    {r \in BagToSet(bag) :
    \E i \in BagToSet(in[p,rply]) : /\ i.res = r.res}

ConsumeRply(p) ==
    /\ MatchesWithIn(p,own[p]) # {}
    /\ LET max == CHOOSE max \in MatchesWithIn(p,own[p]) :
           \A elt \in MatchesWithIn(p,own[p]) : max.pr >= elt.pr
           pkt == CHOOSE pkt \in BagToSet(in[p,rply]) : pkt.res = max.res
       IN /\ trust' = [trust EXCEPT ![p,pkt.src] = Min(@ + c + max.pr,MaxTrust)]
          /\ in' = [in EXCEPT ![p,rply] = Rm(@,pkt)]
          /\ own' = [own EXCEPT ![p] = Rm(@,max)]
          /\ UNCHANGED <<out, relay>>

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
    /\ UNCHANGED own

PrcRply(p) ==
    \/ ConsumeRply(p)
    \/ FrwdRply(p)

Drop(b) ==
    /\ Len(out[b]) # 0
    /\ out' = [out EXCEPT ![b] = Tail(@)]
    /\ UNCHANGED <<in, trust, relay, own>>

CreateByz(b) ==
    /\ \E pkt \in Packet : /\ pkt.src = b
                           /\ out' = [out EXCEPT ![b] = Append(@,pkt)]
                           /\ UNCHANGED <<in, relay, own, trust>>

Next ==
    \/ \E p \in Honest : PrcRqst(p)
    \/ \E p \in Honest : PrcRply(p)
    \/ \E p \in Honest : \E pkt \in Packet : CreateRqst(p,pkt)
    (* send from honest to honest peer *)
    \/ \E src \in Honest :
       \E dst \in Honest \ {src} :
       \E pkt \in Packet : /\ Send(src,pkt)
                           /\ Rcv(dst,pkt)
    (* send from honest to byzantine peer *)
    \/ \E src \in Honest :
       \E dst \in Byzantine : /\ out[src] # << >>
                              /\ out' = [out EXCEPT ![src] = Tail(out[src]),
                                                    ![dst] = Append(@,Head(out[src]))]
                              /\ UNCHANGED <<trust,in,own, relay>>
    (* behaviour of byzantine peer *)
    (* create arbitrary packet, except peer cannot fake others identities *)
    \/ \E b \in Byzantine : CreateByz(b)
    (* drop packet from sending queue *)
    \/ \E b \in Byzantine : Drop(b)
    (* send a packet *)
    \/ \E b \in Byzantine :
       \E dst \in Peers :
       \E pkt \in Packet : /\ Send(b,pkt)
                           /\ Rcv(dst,pkt)

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
RcvEnabled == \E pkt \in Reply : ENABLED Rcv(P,pkt)
SendRcvEnabled == Len(out[P]) # 0 => \E pkt \in Packet :
                                     \E p \in Peers :  /\ ENABLED Send(P,pkt)
                                                       /\ ENABLED Rcv(p,pkt)
CreateEnabled == \A pkt \in Request : (/\ pkt.src = P
                                       /\ pkt.dst # P) => ENABLED CreateRqst(P,pkt)
================================================================================
THEOREM Spec => []TypeInv
================================================================================
