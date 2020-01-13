---- MODULE Peer ---------------------------------------------------------------
EXTENDS Naturals, Sequences, Bags
(* Documentation *)
(* This specification deals WITH request-response protocols, IN which intermediary
   peers can verify that the response corresponds to the request, WITH the goal of
   providing Byzantine fault tolerance and DoS resistance
   in an unpermissioned p2p network. The idea is originally due to a paper of Christian
   Grothoff *)

(* Implicit assumptions include reliable transport layer with zero delay, the neighbour
   a request is forwarded to is irrelevant, no peer can be impersonated (sources are
   cryptographically signed), load is modelled as binary, fixed number of peers
   guaranteed to be honest. *)
--------------------------------------------------------------------------------
VARIABLES buf, chan, track, trust
vars == <<buf, chan, track, trust>>

CONSTANT Priority, P, Honest, Byzantine, Resource, TrustBound, LoadBound, TrackBound, (* Neighbour(_,_), *) BufBound(* , Local *)

Peers == Honest \cup Byzantine
(* could be replaced by a different neighbourship relation *)
Neighbour(p1,p2) == TRUE
(* Local == [e \in Peers |-> {0}] *)
Local == (0 :> {0} @@ 1 :> {1} @@ 2 :> {2})
AXIOM Local[P] \subseteq Resource
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

Init ==
    /\ buf = [p \in Peers |-> EmptyBag]
    /\ track = [p \in Peers |-> EmptyBag]
    /\ trust = [e \in Peers \X Peers |-> 0]
    /\ chan = [e \in Peers \X Peers |-> << >>]

Request == [src : Peers, pr : Priority, res : Resource]
Reply == [res : Resource]
Packet == Request \cup Reply
Value == 0..TrustBound

(* some positive constant, may need to be adapted in an implementation *)
c == 1

RECURSIVE SumTrust(_)
SumTrust(S) ==
    LET elt == CHOOSE e \in S : TRUE
    IN  IF S = {} THEN 0
              ELSE trust[P,elt] + SumTrust(S \ {elt})

(* N == {p \in Peers : Neighbour(P,p)} *)
N == Peers
Min(x, y) == IF x >= y THEN y ELSE x
Max(x, y) == IF x >= y THEN x ELSE y
TotalTrust == Max(SumTrust(N \ {P}),1)
RqstInBuf(pkt) == pkt \in [lasthop : Peers, val : Value, res : Resource]
RplyInBuf(pkt) == pkt \in [lasthop : Peers, res : Resource]
Add(B,elt) == B (+) SetToBag({elt})
Rm(B,elt) == B (-) SetToBag({elt})

RECURSIVE Filter(_,_)
Filter(F(_),bag) ==
    IF bag = EmptyBag
    THEN EmptyBag
    ELSE
    LET e == CHOOSE elt \in BagToSet(bag) : TRUE
    IN IF F(e)
       THEN Add(Filter(F,Rm(bag,e)),e)
       ELSE Filter(F,Rm(bag,e))

Res(x) == x.res
ToSelf(x) == x.nxthop = P
(* IsRqst(x) == x \in Request *)
(* IsRply(x) == x \in Reply *)
IsLocal(x) == x.res \in Local[P]
toself == Filter(ToSelf,track[P])
PNeeds == BagOfAll(Res,toself)
rqsts_in_buf == Filter(RqstInBuf,buf[P])
rplys_in_buf == Filter(RplyInBuf,buf[P])
local == Filter(IsLocal,rqsts_in_buf)
nonlocal == rqsts_in_buf (-) local

(* maximal number of packets P can use locally *)
maxusable == CHOOSE maxusable \in SubBag(rplys_in_buf) :
    /\ BagOfAll(Res,maxusable) \sqsubseteq PNeeds
    /\ \A usable \in SubBag(rplys_in_buf) :
       BagOfAll(Res,usable) \sqsubseteq PNeeds
       => BagCardinality(usable) <= BagCardinality(maxusable)

(* packets P doesn't need *)
unneeded == rplys_in_buf (-) maxusable

(* packets from the unneeded that can be forwarded *)
frwd == CHOOSE frwd \in SubBag(unneeded) :
    /\ BagOfAll(Res,frwd) \sqsubseteq BagOfAll(Res,track[P] (-) toself)
    /\ \A frwdable \in SubBag(unneeded) :
       BagOfAll(Res,frwdable) \sqsubseteq BagOfAll(Res,track[P] (-) toself)
       => BagCardinality(frwdable) <= BagCardinality(frwd)

(* no matching entry *)
discard == unneeded (-) frwd

TypeInv ==
    /\ \A p \in Peers : P # p => trust[P,p] \in 0..TrustBound
    /\ IsABag(track[P])
    /\ \A e \in BagToSet(track[P]) : e \in [nxthop : N, lasthop : N, val : Value, res : Resource]
    /\ IsABag(buf[P])
    /\ \A e \in BagToSet(buf[P]) : e \in [lasthop : Peers, val : Value, res : Resource]
                                 \cup [lasthop : Peers, res : Resource]
    /\ maxusable
       (+) frwd
       (+) local
       (+) nonlocal
       (+) discard = buf[P]
    /\ BagToSet(rplys_in_buf) \subseteq [res : Resource, lasthop : Peers]
    /\ BagToSet(rqsts_in_buf) \subseteq [res : Resource, lasthop : Peers, val : Value]
    (* NOTE unneeded not always empty *)
    (* /\ unneeded = EmptyBag *)
    (* NOTE maxusable not always empty *)
    (* /\ maxusable = EmptyBag *)
    (* NOTE local not always empty *)
    (* /\ local = EmptyBag *)
    (* NOTE nonlocal not always empty *)
    (* /\ nonlocal = EmptyBag *)
    (* /\ BagCardinality(PNeeds) = BagCardinality(track[P]) *)

--------------------------------------------------------------------------------

Rcv(n) ==
    LET pkt == Head(chan[n,P])
        Malformed(x) == /\ x \notin Request
                        /\ x \notin Reply
        From(x) == x.lasthop = n
        RqstsFrom == Filter(From,rqsts_in_buf)
        RplysFrom == Filter(From,rplys_in_buf)
    IN
    (* if P wants to make a request, packets from other peers are blocked from
       being buffered, until the requests of P are added to the buffer, after which
       buffering of other packets is resumed *)
    \/ /\ n = P
       /\ chan[P,P] # << >>
       /\ BagCardinality(buf[P]) < BufBound
       /\ buf' = [buf EXCEPT ![P] = Add(@,[lasthop |-> pkt.src, val |-> pkt.pr, res |-> pkt.res])]
       /\ chan' = [chan EXCEPT ![P,P] = Tail(@)]
       /\ UNCHANGED <<track, trust>>
    \/ /\ chan[P,P] = << >>
       /\ chan[n,P] # << >>
       /\ \/ /\ pkt \in Request
             /\ pkt.src = n
             /\ \/ /\ BagCardinality(buf[P]) >= LoadBound
                   /\ BagCardinality(RqstsFrom) < (BufBound(* .rqst *) * trust[P,n]) \div TotalTrust
                   /\ buf' = [buf EXCEPT ![P] = Add(@,[lasthop |-> n,
                                                       val |-> Min(trust[P,n],pkt.pr),
                                                       res |-> pkt.res])]
                   /\ chan' = [chan EXCEPT ![n,P] = Tail(@)]
                \/ /\ BagCardinality(buf[P]) >= LoadBound
                   /\ BagCardinality(RqstsFrom) >= (BufBound(* .rqst *) * trust[P,n]) \div TotalTrust
                   /\ UNCHANGED <<buf, chan>>
                \/ /\ BagCardinality(buf[P]) < LoadBound
                   /\ buf' = [buf EXCEPT ![P] = Add(@,[lasthop |-> n,
                                                       val |-> pkt.pr,
                                                       res |-> pkt.res])]
                   /\ chan' = [chan EXCEPT ![n,P] = Tail(@)]
             /\ UNCHANGED <<track, trust>>
          \/ /\ pkt \in Reply
             /\ \/ /\ BagCardinality(RqstsFrom) < Max((BufBound(* .rply *) * trust[P,n]) \div TotalTrust,1)
                   /\ buf' = [buf EXCEPT ![P] = Add(@,[lasthop |-> n,
                                                       res |-> pkt.res])]
                   /\ chan' = [chan EXCEPT ![n,P] = Tail(@)]
                \/ /\ BagCardinality(RqstsFrom) >= Max((BufBound(* .rply *) * trust[P,n]) \div TotalTrust,1)
                   /\ UNCHANGED <<buf, chan>>
             /\ UNCHANGED <<track, trust>>
          (* if packet is malformed or doesn't originate from last hop, discard *)
          \/ /\ \/ Malformed(pkt)
                \/ /\ pkt \in Request
                   /\ pkt.src # n
             /\ chan' = [chan EXCEPT ![n,P] = Tail(@)]
             /\ UNCHANGED <<buf, track, trust>>

(* assumes all elements of the bag sub can be found locally,
   sends replies to all elements in sub *)
Rply(rqst_in_buf) ==
    /\ chan' = [chan EXCEPT ![P,rqst_in_buf.lasthop] = Append(@,[res |-> rqst_in_buf.res])]
    /\ buf' = [buf EXCEPT ![P] = Rm(@,rqst_in_buf)]
    /\ UNCHANGED <<track, trust>>

Relay(rqst_in_buf) ==
    /\ \E n \in N \ {P} :
        /\ track' = [track EXCEPT ![P] = Add(@,[nxthop |-> rqst_in_buf.lasthop,
                                                lasthop |-> n,
                                                val |-> rqst_in_buf.val,
                                                res |-> rqst_in_buf.res])]
        /\ chan' = [chan EXCEPT ![P,n] = Append(@,[src |-> P,
                                                   pr |-> IF rqst_in_buf.lasthop = P
                                                          THEN rqst_in_buf.val
                                                          ELSE 0,
                                                   res |-> rqst_in_buf.res])]
    /\ buf' = [buf EXCEPT ![P] = Rm(@,rqst_in_buf)]
    /\ trust' = [trust EXCEPT ![P,rqst_in_buf.lasthop] = Max(0,@ - rqst_in_buf.val)]

FrwdRply(rply_in_buf) ==
    LET
    Match(entry) == entry.res = rply_in_buf.res
    match == Filter(Match,track[P])
    IN
    \/ /\ \E entry \in BagToSet(track[P]) :
           /\ entry.lasthop = rply_in_buf.lasthop
           /\ entry.res = rply_in_buf.res
           /\ trust' = [trust EXCEPT ![P,rply_in_buf.lasthop] = Min(TrustBound,@ + c + entry.val)]
           /\ track' = [track EXCEPT ![P] = Rm(@,entry)]
           /\ chan' = [chan EXCEPT ![P,entry.nxthop] = Append(@,[res |-> rply_in_buf.res])]
       /\ buf' = [buf EXCEPT ![P] = Rm(@,rply_in_buf)]
    \/ /\ ~ \E exact \in BagToSet(track[P]) :
           /\ exact.lasthop = rply_in_buf.lasthop
           /\ exact.res = rply_in_buf.res
       /\ \E entry \in BagToSet(track[P]) :
           /\ entry.res = rply_in_buf.res
           /\ trust' = [trust EXCEPT ![P,rply_in_buf.lasthop] = Min(TrustBound,@ + c + entry.val)]
           /\ track' = [track EXCEPT ![P] = Rm(@,entry)]
           /\ chan' = [chan EXCEPT ![P,entry.nxthop] = Append(@,[res |-> rply_in_buf.res])]
       /\ buf' = [buf EXCEPT ![P] = Rm(@,rply_in_buf)]

CreateRqst(rqst) ==
    (* valid requests created by P must be for resources not locally available
       and signed by P *)
    /\ rqst.res \notin Local[P]
    /\ rqst.src = P
    /\ chan' = [chan EXCEPT ![P,P] = Append(@,rqst)]
    /\ UNCHANGED <<buf, track, trust>>

Consume(rply_in_buf) ==
    LET
    Track == BagToSet(track[P])
    (* Match(entry) == entry.res = rply_in_buf.res *)
    (* all the tracked packets that match the resource *)
    matches == Filter(LAMBDA e : e.res = rply_in_buf.res,track[P])
    Matches == BagToSet(matches)
    (* all the tracked packets that match the resource and are expected to come
       from the peer that sent the reply *)
    knownlast == Filter(LAMBDA e : e.lasthop = rply_in_buf.lasthop,matches)
    Knownlast == BagToSet(knownlast)
    knownlast_to_P == Filter(LAMBDA e : e.nxthop = P,knownlast)
    Knownlast_To_P == BagToSet(knownlast_to_P)
    IN
    /\ IF knownlast = EmptyBag
       THEN \E entry \in Matches : /\ entry.nxthop = P
                                   /\ track' = [track EXCEPT ![P] = Rm(@,entry)]
                                   /\ trust' = [trust EXCEPT ![P,rply_in_buf.lasthop] = Min(@ + c + entry.val,TrustBound)]
       ELSE IF knownlast_to_P # EmptyBag
            THEN \E entry \in Knownlast_To_P :
                  /\ track' = [track EXCEPT ![P] = Rm(@,entry)]
                  /\ trust' = [trust EXCEPT ![P,rply_in_buf.lasthop] = Min(@ + c + entry.val,TrustBound)]
            ELSE \E steal \in Knownlast :
                 \E own \in Matches :
                  /\ own.nxthop = P
                  /\ track' = [track EXCEPT ![P] = Add(Rm(Rm(@,steal),own),[steal EXCEPT !.lasthop = own.lasthop, !.val = own.val])]
                  /\ trust' = [trust EXCEPT ![P,rply_in_buf.lasthop] = Min(@ + c + steal.val,TrustBound)]
    /\ buf' = [buf EXCEPT ![P] = Rm(@,rply_in_buf)]
    /\ UNCHANGED chan


Drop(rply_in_buf) ==
    /\ buf' = [buf EXCEPT ![P] = Rm(@,rply_in_buf)]
    /\ UNCHANGED <<chan, track, trust>>

Process(pkt) ==
    IF pkt \in [lasthop : N, res : Resource, val : Value]
    THEN IF pkt.res \in Local[P]
         THEN Rply(pkt)
         ELSE Relay(pkt)
    ELSE IF pkt \in [lasthop : N, res : Resource]
         THEN IF BagIn(pkt.res,PNeeds)
              THEN Consume(pkt)
              ELSE IF ~ BagIn(pkt.res,BagOfAll(Res,track[P]))
                   THEN Drop(pkt)
                   ELSE FrwdRply(pkt)
         ELSE Drop(pkt)

Next ==
   LET e == CHOOSE elt \in Peers \X Peers : elt[1] # elt[2]
   IN
   (* for printing debug statements *)
   (* /\ Print(PNeeds(\* [e[1](\\* ,e[2] *\\)] *\),TRUE) *)
   /\ \/ FALSE
      \/ \E rqst \in Request : CreateRqst(rqst)
      \/ \E n \in N : Rcv(n)
      (* a subset of the packets will be blocked due to IO constraints or TrackBound,
         the complement of which are the free packets *)
         \/ \E pkt \in BagToSet(buf[P]) :
             Process(pkt)

(* packets in buf can always be processed *)
AllPktsEnabled ==
    buf[P] # EmptyBag => \A pkt \in BagToSet(buf[P]) : ENABLED Process(pkt)

Fairness ==
    /\ \A n \in N : WF_vars(Rcv(n))
    /\ \A rqst \in Request : WF_vars(CreateRqst(rqst))
    /\ \A pkt \in BagToSet(buf[P]) :
       /\ WF_vars(Consume(pkt))
       /\ WF_vars(FrwdRply(pkt))
       /\ WF_vars(Rply(pkt))
       /\ WF_vars(Relay(pkt))
       /\ WF_vars(Drop(pkt))

Spec == Init /\ [][Next]_vars /\ Fairness
=======================================================
