---- MODULE Peer ---------------------------------------------------------------
EXTENDS Naturals, Sequences, Bags
(* Documentation *)
(* This specification deals with the handling of packets according to an incentive
   scheme, with the goal of providing Byzantine fault tolerance and DoS resistance
   in an unpermissioned p2p network. The idea is originally due to a paper of Christian
   Grothoff *)

(* Implicit assumptions include reliable transport layer, the neighbour
   a request is forwarded to is irrelevant, no peer can be impersonated (sources are
   cryptographically signed), load is modelled as binary, fixed number of peers guaranteed
   to be honest. *)
--------------------------------------------------------------------------------
VARIABLES buf, chan, track, trust
vars == <<buf, chan, track, trust>>

CONSTANT Priority, P, Honest, Byzantine, Resource, TrustBound, LoadBound, TrackBound, Neighbour(_,_), BufBound, Local

AXIOM Local \subseteq Resource
Peers == Honest \cup Byzantine
AXIOM P \in Honest
AXIOM Honest \cap Byzantine = {}

(* neighbour is a symmetric relation *)
AXIOM /\ \A p \in Peers : Neighbour(p,p)
      /\ \A p1 \in Peers :
         \A p2 \in Peers :
         Neighbour(p1,p2) <=> Neighbour(p2,p1)

(* network is connected *)
AXIOM \A p1 \in Peers :
      \A p2 \in Peers :
      \E path \in Seq(Peers) :
      /\ path[1] = p1
      /\ path[Len(path)] = p2
      /\ \A i \in 1..Len(path)-1 : Neighbour(path[i],path[i+1])

(* Honest peers form a connected subnetwork *)
AXIOM \A p1 \in Honest :
      \A p2 \in Honest :
      \E path \in Seq(Honest) :
      /\ path[1] = p1
      /\ path[Len(path)] = p2
      /\ \A i \in 1..Len(path)-1 : Neighbour(path[i],path[i+1])

Request == [src : Peers, pr : Priority, res : Resource]
Reply == [res : Resource]
Packet == Request \cup Reply
Value == 0..TrustBound
c == 1

LOCAL Sum(f) ==
(******************************************************************)
(* The sum of f[x] for all x IN DOMAIN f.  The definition assumes *)
(* that f is a Nat-valued function and that f[x] equals 0 for all *)
(* but a finite number of elements x IN DOMAIN f.                 *)
(******************************************************************)
LET DSum[S \in SUBSET DOMAIN f] ==
LET elt == CHOOSE e \in S : TRUE
IN  IF S = {} THEN 0
              ELSE f[elt] + DSum[S \ {elt}]
IN  DSum[DOMAIN f]

TotalTrust == Sum(trust)
RqstInBuf(pkt) == pkt \in [lasthop : Peers, val : Value, res : Resource]
RplyInBuf(pkt) == pkt \in [lasthop : Peers, res : Resource]
Add(B,elt) == B (+) SetToBag({elt})
Rm(B,elt) == B (-) SetToBag({elt})
Min(x, y) == IF x >= y THEN y ELSE x
Max(x, y) == IF x >= y THEN x ELSE y
(* EUniqueMin(B) == \E min \in BagToSet(B) : \A elt \in BagToSet(B) : min.val < elt.val *)
(* GetUniqueMin(B) == CHOOSE min \in BagToSet(B) : \A elt \in BagToSet(B) : min.val < elt.val *)
(* EMax(B) == \E max \in BagToSet(B) : \A elt \in BagToSet(B) : elt.val <= max.val *)
(* GetMax(B) == CHOOSE max \in BagToSet(B) : \A elt \in BagToSet(B) : elt.val <= max.val *)
(* EffPriority(p,pkt) == Min(pkt.pr, trust[p,pkt.src]) *)
(* Debit(p,pkt) == [trust EXCEPT ![p,pkt.src] = Max(0, @ - IF pkt \in Request THEN pkt.pr ELSE c)] *)
(* Credit(p,pkt) == [trust EXCEPT ![p,pkt.src] = Min(@ + pkt.pr, TrustBound) ] *)
N == {p \in Peers : Neighbour(P,p)}

Filter(F(_),bag) == [e \in BagToSet(bag) |-> IF F(e) THEN bag[e] ELSE 0]

Res(x) == x.res
ToSelf(x) == x.nxthop = P
(* IsRqst(x) == x \in Request *)
(* IsRply(x) == x \in Reply *)
IsLocal(x) == x.res \in Local
PNeeds == BagOfAll(Res,Filter(ToSelf,track))
rqsts_in_buf == Filter(RqstInBuf,buf)
rplys_in_buf == Filter(RplyInBuf,buf)
local == Filter(IsLocal,rqsts_in_buf)
nonlocal == rqsts_in_buf (-) local

(* maximal number of packets P can use locally *)
maxusable == CHOOSE maxusable \in SubBag(rplys_in_buf) :
    /\ maxusable \sqsubseteq PNeeds
    /\ \A usable \in SubBag(rplys_in_buf) :
       usable \sqsubseteq PNeeds
       => BagCardinality(usable) <= BagCardinality(maxusable)

(* packets P doesn't need *)
unneeded == rplys_in_buf (-) maxusable

(* packets from the unneeded that can be forwarded *)
frwd == CHOOSE frwd \in SubBag(unneeded) :
    /\ frwd \sqsubseteq BagOfAll(Res,track (-) Filter(ToSelf,track))
    /\ \A frwdable \in SubBag(unneeded) :
       frwdable \sqsubseteq BagOfAll(Res,track (-) Filter(ToSelf,track))
       => BagCardinality(frwdable) <= BagCardinality(frwd)

(* no matching entry *)
discard == unneeded (-) frwd

(* TypeInv == *)
(*     /\ \A p \in Peers : P # p => trust[p] \in 0..TrustBound *)
(*     /\ IsABag(track) *)
(*     /\ \A e \in BagToSet(track) : e \in [nxthop : N, lasthop : N, val : Value, res : Resource] *)
(*     /\ IsABag(buf) *)
(*     /\ \A e \in BagToSet(buf) : e \in [lasthop : Peers, val : Value, res : Resource] *)
(*                                  \cup [lasthop : Peers, res : Resource] *)

--------------------------------------------------------------------------------

(* Init == *)
    (* /\ buf = EmptyBag *)
    (* /\ track = EmptyBag *)
    (* /\ trust = [n \in N \ {P} |-> 0] *)

Rcv(n) ==
    LET pkt == Head(chan[n,P])
        Malformed(x) == /\ x \notin Request
                        /\ x \notin Reply
        RqstsFrom(x) == [e \in BagToSet(rqsts_in_buf) |-> IF e.src = x THEN rqsts_in_buf[e] ELSE 0]
        RplysFrom(x) == [e \in BagToSet(rplys_in_buf) |-> IF e.src = x THEN rplys_in_buf[e] ELSE 0]
    IN
    (* if P wants to make a request, packets from other peers are blocked from
       being buffered, until the requests of P are added to the buffer, after which
       buffering of other packets is resumed *)
    \/ /\ n = P
       /\ chan[P,P] # << >>
       /\ BagCardinality(buf) < BufBound
       /\ buf' = Add(buf,Head(chan[P,P]))
       /\ chan' = [chan EXCEPT ![P,P] = Tail(@)]
    \/ /\ chan[P,P] = << >>
       /\ chan[n,P] # << >>
       /\ \/ /\ pkt \in Request
             /\ pkt.src = n
             /\ BagCardinality(RqstsFrom(n)) < (BufBound.rqst * trust[n]) \div TotalTrust
             /\ Add(buf,[lasthop |-> pkt.src, val |-> Min(trust[n],pkt.pr), res |-> pkt.res])
             /\ UNCHANGED <<track, trust>>
          \/ /\ pkt \in Reply
             /\ BagCardinality(RplysFrom(n)) < (BufBound.rply * trust[n]) \div TotalTrust
             /\ Add(buf,[lasthop |-> n, res |-> pkt.res])
             /\ UNCHANGED <<track, trust>>
          (* if packet is malformed or doesn't originate from last hop, discard *)
          \/ /\ \/ Malformed(pkt)
                \/ pkt.src # n
             /\ chan' = [chan EXCEPT ![n,P] = Tail(@)]
             /\ UNCHANGED <<buf, track, trust>>

(* assumes all elements of the bag sub can be found locally,
   sends replies to all elements in sub *)
Rply(rqst_in_buf) ==
    /\ chan' = [chan EXCEPT ![P,rqst_in_buf.lasthop] = Append(@,[res |-> rqst_in_buf.res])]
    /\ buf' = Rm(buf,rqst_in_buf)
    /\ UNCHANGED <<track, trust>>

Relay(rqst_in_buf) ==
    /\ BagCardinality(track) = TrackBound
    /\ \E n \in N \ {P} : /\ track' = Add(track,[nxthop |-> rqst_in_buf.lasthop,
                                                 lasthop |-> n,
                                                 value |-> 0,
                                                 res |-> rqst_in_buf.res])
                          /\ chan' = [chan EXCEPT ![P,n] = Append(@,[res |-> rqst_in_buf.res])]
    /\ buf' = Rm(buf,rqst_in_buf)
    /\ trust' = [trust EXCEPT ![rqst_in_buf.lasthop] = Max(0,@ - rqst_in_buf.val)]

FrwdRply(rply_in_buf) ==
    (* remove all the processed plus discarded packets from the buffer *)
    /\ BagCardinality(track) < TrackBound
    /\ \E entry : /\ BagIn(entry,track)
                  /\ entry.lasthop = rply_in_buf.src
                  /\ trust' = [trust EXCEPT ![rply_in_buf.src] = Min(TrustBound,@ + c + entry.val)]
                  /\ track' = Rm(track,entry)
                  /\ chan' = [chan EXCEPT ![P,entry.nxthop] = Append(@,[res |-> rply_in_buf.res])]
    /\ buf' = Rm(buf,rply_in_buf)

CreateRqst(rqst_in_buf) ==
    (* valid requests created by P must be for resources not locally available
       and signed by P *)
    /\ rqst_in_buf.res \notin Local
    /\ rqst_in_buf.src = P
    /\ chan' = [chan EXCEPT ![P,P] = Append(@,rqst_in_buf)]
    /\ UNCHANGED <<buf, track, trust>>

Consume(rply_in_buf) ==
    (* entry was addressed to P *)
    \/ /\ \E entry \in BagToSet(track) : /\ entry.nxthop = P
                                         /\ entry.lasthop = rply_in_buf.src
                                         /\ trust' = [trust EXCEPT ![entry.src] = Min(TrustBound,@ + c + entry.val)]
                                         /\ track' = Rm(track,entry)
       /\ buf' = Rm(buf,rply_in_buf)
    (* entry wasn't adressed to P, self-interest dictates P 'steals' the answer *)
    \/ /\ ~ \E entry \in BagToSet(track) : /\ entry.nxthop = P
                                           /\ entry.lasthop = rply_in_buf.src
       (* adapt tracked packets, swapping *)
       /\ \E own \in BagToSet(track) :
          \E stolen \in BagToSet(track) :
          /\ track' = Add(Rm(Rm(track,stolen),own),[own EXCEPT !.nxthop = stolen.nxthop])
          /\ trust' = [trust EXCEPT ![rply_in_buf.src] = Max(TrustBound,@ + c + stolen.val)]
       /\ buf' = Rm(buf,rply_in_buf)

Drop(rply_in_buf) ==
    /\ buf' = Rm(buf,rply_in_buf)
    /\ UNCHANGED <<chan, track, trust>>

Next ==
    (* a subset of the packets will be blocked due to IO constraints or TrackBound,
       the complement of which are the free packets *)
    \/ \E free \in [maxusable : SubBag(maxusable),
                    frwd : SubBag(frwd),
                    local : SubBag(local),
                    nonlocal : SubBag(nonlocal)] :
       \/ \E pkt \in BagToSet(free.maxusable) : Consume(pkt)
       \/ \E pkt \in BagToSet(free.frwd) : FrwdRply(pkt)
       \/ \E pkt \in BagToSet(free.local) : Rply(pkt)
       (*TODO*)
       \/ \E pkt \in BagToSet(free.nonlocal) : Relay(pkt)
       \/ \E pkt \in BagToSet(discard) : Drop(pkt)
    \/ \E n \in N : Rcv(n)
    \/ \E rqst \in Request : CreateRqst(rqst)

Fairness ==
    (* /\ \A pkts \in SubBag(buf) : WF_vars(Process(pkts)) *)
    /\ \A n \in N : WF_vars(Rcv(n))

(* Spec == Init /\ [][Next]_vars /\ Fairness *)
=======================================================
