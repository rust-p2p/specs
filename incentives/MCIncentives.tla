---- MODULE MCIncentives ----
EXTENDS Incentives

Constraint1 ==
    /\ \A p \in Peers : Len(chan[p]) <= 1

Constraint2 ==
    /\ \A p \in Peers : BagCardinality(relay[p]) <= 1

Constraint3 ==
    /\ \A p \in Peers : BagCardinality(own[p]) <= 1

RcvEnabled == \E p \in Peers : Len(chan[P]) # 0 => ENABLED Rcv(P,p)

OnlyOneRcvRqstEnabled == \E p \in Peers \ {P}:
                             LET pkt == Head(chan[P])
                             IN
                             /\ chan[P] # << >>
                             /\ pkt \in Request
                             =>
                             \/ /\ ENABLED RcvRqstLowLoad(p,pkt)
                                /\ ~ ENABLED RcvRqstHighLoad(p,pkt)
                                /\ ~ ENABLED RcvRqstLimit(p,pkt)
                             \/ /\ ~ ENABLED RcvRqstLowLoad(p,pkt)
                                /\ ENABLED RcvRqstHighLoad(p,pkt)
                                /\ ~ ENABLED RcvRqstLimit(p,pkt)
                             \/ /\ ~ ENABLED RcvRqstLowLoad(p,pkt)
                                /\ ~ ENABLED RcvRqstHighLoad(p,pkt)
                                /\ ENABLED RcvRqstLimit(p,pkt)

OnlyOneRcvRplyEnabled == \E p \in Peers \ {P} :
                             LET pkt == Head(chan[P])
                             IN
                             /\ chan[P] # << >>
                             /\ pkt \in Reply
                             =>
                             \/ /\ ENABLED RcvRply(p,pkt)
                                /\ ~ ENABLED RcvRplyLimit(p,pkt)
                             \/ /\ ~ ENABLED RcvRply(p,pkt)
                                /\ ENABLED RcvRplyLimit(p,pkt)

CreateEnabled == ENABLED CreateRqst(P)
====
