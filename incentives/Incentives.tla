---- MODULE Incentives -----------------------------------------------------
EXTENDS Naturals, Sequences, Bags
(* Documentation *)
(* This specification deals with the handling of packets according to an incentive
   scheme, with the goal of providing Byzantine fault tolerance and DoS resistance
   in an unpermissioned p2p network. The idea is originally due to a paper of Christian
   Grothoff *)

(* Implicit assumptions include reliable transport layer with no delay, the neighbour
   a request is forwarded to is irrelevant, no peer can be impersonated (sources are
   cryptographically signed), load is modelled as binary, fixed number of peers guaranteed
   to be honest.
   Due to symmetry only the invariants of an honest peer P are checked. *)
--------------------------------------------------------------------------------
VARIABLES buf, chan, own, relay, trust
vars == <<buf, chan, own, relay, trust>>

CONSTANT P, Honest, Byzantine, Resources, Priority, MaxTrust, LoadBound

AXIOM P \in Honest

Peers == Honest \cup Byzantine
MaxBuf == [rqst |-> 2, rply |-> 2]
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
    /\ \A p \in Peers : /\ P # p => trust[P,p] \in 0..MaxTrust
    /\ IsABag(relay[P])
    /\ \A elt \in BagToSet(relay[P]) : elt \in Request
    /\ \A t \in Type : IsABag(buf[P,t])
    /\ \A elt \in BagToSet(buf[P,rqst]) :
                                                (* elt \in Packet \X 0..MaxTrust ? *)
                                                            /\ elt[1] \in Request
                                                            /\ elt[2] \in 0..MaxTrust
                                                            /\ Len(elt) = 2
    /\ \A elt \in BagToSet(buf[P,rply]) : elt \in Reply
    /\ chan \in [Peers -> Seq(Packet)]
    /\ IsABag(own[P])
    /\ \A elt \in BagToSet(own[P]) : elt \in [res : Resources, pr : Priority]

--------------------------------------------------------------------------------

Init ==
    /\ relay = [h \in Honest |-> EmptyBag]
    /\ buf = [elt \in Honest \X Type |-> EmptyBag]
    /\ chan = [p \in Peers |-> << >>]
    /\ trust = [<<p1,p2>> \in Honest \X Peers |-> IF p1 = p2 THEN MaxTrust + 1 ELSE 0]
    /\ own = [h \in Honest |-> EmptyBag]

(* Don't charge trust when load low *)
RcvRqstLowLoad(rcv,pkt) ==
    /\ BagCardinality(buf[rcv,rqst]) < LoadBound
    /\ buf' = [buf EXCEPT ![rcv,rqst] = Add(@,<<pkt,0>>)]
    /\ UNCHANGED <<own, relay, trust>>

(* If enough packets buf buffer start charging trust *)
RcvRqstHighLoad(rcv,pkt) ==
    /\ BagCardinality(buf[rcv,rqst]) >= LoadBound
    /\ BagCardinality(buf[rcv,rqst]) < MaxBuf.rqst
    /\ buf' = [buf EXCEPT ![rcv,rqst] = Add(@, <<pkt, EffPriority(rcv,pkt)>>)]
    /\ trust' = Debit(rcv,pkt,rqst)
    /\ UNCHANGED <<own, relay>>

(* If max packets buf buffer start exchanging them, adapting trust accordingly *)
RcvRqstLimit(rcv,pkt) ==
    /\ BagCardinality(buf[rcv,rqst]) = MaxBuf.rqst
    /\ \/ /\ \E min \in BagToSet(buf[rcv,rqst]) : min[2] < EffPriority(rcv,pkt)
          /\ LET min == CHOOSE min \in BagToSet(buf[rcv,rqst]) : min[2] < EffPriority(rcv,pkt)
             IN /\ buf' = [buf EXCEPT ![rcv,rqst] = Swap(@,min,<<pkt,EffPriority(rcv,pkt)>>)]
                /\ trust' = [Debit(rcv,pkt,rqst) EXCEPT ![rcv,min[1].src] = Min(@ + min[2],MaxTrust)]
       \/ /\ ~\E min \in BagToSet(buf[rcv,rqst]) : min[2] < EffPriority(rcv,pkt)
          /\ UNCHANGED <<trust, buf>>
    /\ UNCHANGED <<own, relay>>

(* If enough packets buf buffer start charging trust *)
RcvRply(rcv,pkt) ==
    LET Eq(x) == x.res = pkt.res
        NrMatch(B) == BagCardinality(BagOfAll(Eq,B))
    IN
    \/ /\ NrMatch(own[rcv]) + NrMatch(relay[rcv]) > NrMatch(buf[rcv,rply])
       /\ BagCardinality(buf[rcv,rply]) < MaxBuf.rply
       /\ buf' = [buf EXCEPT ![rcv,rply] = Add(buf[rcv,rply], pkt)]
       /\ trust' = Debit(rcv,pkt,rply)
       /\ UNCHANGED <<own, relay>>
    \/ /\ NrMatch(own[rcv]) + NrMatch(relay[rcv]) <= NrMatch(buf[rcv,rply])
       /\ BagCardinality(buf[rcv,rply]) < MaxBuf.rply
       /\ UNCHANGED <<buf, own, relay, trust>>

(* If max packets buf buffer start exchanging them, adapting trust accordingly *)
RcvRplyLimit(rcv,pkt) ==
    LET Eq(x) == x.res = pkt.res
        NrMatch(B) == BagCardinality(BagOfAll(Eq,B))
    IN
    \/ /\ NrMatch(own[rcv]) + NrMatch(relay[rcv]) > NrMatch(buf[rcv,rply])
       /\ BagCardinality(buf[rcv,rply]) = MaxBuf.rply
       /\ \/ /\ \E min \in BagToSet(buf[rcv,rply]) : trust[rcv,min.src] < trust[rcv,pkt.src]
             /\ LET min == CHOOSE min \in BagToSet(buf[rcv,rply]) : trust[rcv,min.src] < trust[rcv,pkt.src]
                IN /\ buf' = [buf EXCEPT ![rcv,rply] = Swap(@,min,pkt)]
                   /\ trust' = [Debit(rcv,pkt,rply) EXCEPT ![rcv,min.src] = Min(@ + c,MaxTrust)]
          \/ /\ ~ \E min \in BagToSet(buf[rcv,rply]) : trust[rcv,min.src] < trust[rcv,pkt.src]
             /\ UNCHANGED <<buf, trust>>
       /\ UNCHANGED <<own, relay>>
    \/ /\ NrMatch(own[rcv]) + NrMatch(relay[rcv]) <= NrMatch(buf[rcv,rply])
       /\ BagCardinality(buf[rcv,rply]) = MaxBuf.rply
       /\ UNCHANGED <<buf, own, relay, trust>>

(* Receive the packet at rcv *)
Rcv(snd,rcv) ==
    LET pkt == Head(chan[snd])
    IN /\ chan[snd] # << >>
       /\ chan' = [chan EXCEPT ![snd] = Tail(chan[snd])]
       /\ UNCHANGED <<own, relay>>
       /\ \/ /\ pkt \in Request
             /\ \/ RcvRqstLowLoad(rcv,pkt)
                \/ RcvRqstHighLoad(rcv,pkt)
                \/ RcvRqstLimit(rcv,pkt)
          \/ /\ pkt \in Reply
             /\ \/ RcvRply(rcv,pkt)
                \/ RcvRplyLimit(rcv,pkt)

(* for testing purposes it's helpful to have operators without existential quantifier *)
CreateRqstArg(p,pkt) ==
    /\ pkt \in Request
    /\ pkt.src = p
    /\ pkt.dst # p
    /\ chan' = [chan EXCEPT ![p] = Append(chan[p],pkt)]
    /\ own' = [own EXCEPT ![p] = Add(@,[res |-> pkt.res, pr |-> pkt.pr])]
    /\ UNCHANGED <<buf, relay, trust>>

CreateRqst(p) ==
    \E pkt \in Request :
    CreateRqstArg(p,pkt)

(* relay a request *)
Relay(p,nxt) ==
    /\ buf[p,rqst] # EmptyBag
    /\ LET Buf == BagToSet(buf[p,rqst])
           max == CHOOSE max \in Buf : \A elt \in Buf : max[2] >= elt[2]
           pkt == max[1]
       IN /\ relay' = [relay EXCEPT ![p] = Add(@,[pkt EXCEPT !.dst = p,
                                                             !.pr = max[2]])]
          /\ chan' = [chan EXCEPT ![p] = Append(@,[src |-> p,
                                                   dst |-> nxt,
                                                   pr |-> 0,
                                                   res |-> pkt.res])]
          /\ buf' = [buf EXCEPT ![p,rqst] = Rm(@,max)]
          /\ UNCHANGED <<own, trust>>

(* reply to a request *)
Rply(p) ==
    /\ buf[p,rqst] # EmptyBag
    /\ LET Buf == BagToSet(buf[p,rqst])
           (* choose packet with maximal priority *)
           max == CHOOSE max \in Buf : \A elt \in Buf : max[2] >= elt[2]
           pkt == max[1]
           answer == [src |-> p, dst |-> pkt.src, res |-> pkt.res]
       IN /\ chan' = [chan EXCEPT ![p] = Append(@,answer)]
          /\ buf' = [buf EXCEPT ![p,rqst] = Rm(@,max)]
          /\ UNCHANGED <<own, relay, trust>>

PrcRqst(p) ==
    \/ Rply(p)
    (* next peer cannot be the same one that processed the request *)
    \/ \E nxt \in Peers \ {p} : Relay(p,nxt)

MatchesWithIn(p,bag) ==
    {r \in BagToSet(bag) :
    \E i \in BagToSet(buf[p,rply]) : i.res = r.res}

ConsumeRply(p) ==
    /\ MatchesWithIn(p,own[p]) # {}
    /\ LET max == CHOOSE max \in MatchesWithIn(p,own[p]) :
           \A elt \in MatchesWithIn(p,own[p]) : max.pr >= elt.pr
           pkt == CHOOSE pkt \in BagToSet(buf[p,rply]) : pkt.res = max.res
       IN /\ trust' = [trust EXCEPT ![p,pkt.src] = Min(@ + c + max.pr,MaxTrust)]
          /\ buf' = [buf EXCEPT ![p,rply] = Rm(@,pkt)]
          /\ own' = [own EXCEPT ![p] = Rm(@,max)]
          /\ UNCHANGED <<chan, relay>>

FrwdRply(p) ==
    (* buf not empty, pick response to packet with maximum priority *)
    /\ buf[p,rply] # EmptyBag
    /\ \E max \in MatchesWithIn(p,relay[p]) :
       \A elt \in MatchesWithIn(p,relay[p]) : max.pr >= elt.pr
    /\ LET max == CHOOSE max \in MatchesWithIn(p,relay[p]) :
                      \A elt \in MatchesWithIn(p,relay[p]) : max.pr >= elt.pr
           frwd == [max EXCEPT !.src = p, !.dst = max.src]
       IN /\ relay' = [relay EXCEPT ![p] = Rm(@,max)]
          /\ buf' = [buf EXCEPT ![p,rply] = Rm(@,max)]
          /\ chan' = [chan EXCEPT ![p] = Append(@,frwd)]
          /\ trust' = [trust EXCEPT ![p,max.src] = Min(@ + c,MaxTrust)]
    /\ UNCHANGED own

PrcRply(p) ==
    \/ ConsumeRply(p)
    \/ FrwdRply(p)

Drop(b) ==
    /\ Len(chan[b]) # 0
    /\ chan' = [chan EXCEPT ![b] = Tail(@)]
    /\ UNCHANGED <<buf, own, relay, trust>>

CreateByz(b) ==
    \E pkt \in Packet : /\ pkt.src = b
                        /\ chan' = [chan EXCEPT ![b] = Append(@,pkt)]
                        /\ UNCHANGED <<buf, own, relay, trust>>

Next ==
    \/ \E h \in Honest : PrcRqst(h)
    \/ \E h \in Honest : PrcRply(h)
    \/ \E h \in Honest : CreateRqst(h)
    (* send from honest to honest peer *)
    \/ \E snd \in Honest :
       \E rcv \in Honest \ {snd} :
       Rcv(snd,rcv)
    (* send from honest to byzantine peer *)
    \/ \E snd \in Honest :
       \E rcv \in Byzantine :
       /\ chan[snd] # << >>
       /\ chan' = [chan EXCEPT ![snd] = Tail(@),
                               ![rcv] = Append(@,Head(chan[snd]))]
       /\ UNCHANGED <<buf, own, relay, trust>>
    (* behaviour of byzantine peer *)
    (* create arbitrary packet, except peer cannot fake others identities *)
    \/ \E b \in Byzantine : CreateByz(b)
    (* drop packet from sending queue *)
    \/ \E b \in Byzantine : Drop(b)
    (* send a packet *)
    \/ \E snd \in Byzantine :
       \E rcv \in Peers : Rcv(snd,rcv)

Fairness ==
    \A p \in Peers :
    /\ WF_vars(PrcRqst(p))
    /\ WF_vars(PrcRply(p))
    /\ WF_vars(CreateRqst(p))
    /\ WF_vars(ConsumeRply(p))
    /\ \A snd \in Peers :
       \A rcv \in Peers :
       WF_vars(Rcv(snd,rcv))

Spec == Init /\ [][Next]_vars /\ Fairness

================================================================================
THEOREM Spec => []TypeInv
================================================================================
