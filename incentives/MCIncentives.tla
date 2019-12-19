---- MODULE MCIncentives ----
EXTENDS Incentives

Constraint ==
    /\ \A <<p,t>> \in Peers \X Type : BagCardinality(in[p,t]) <= 1

Constraint1 ==
    /\ \A p \in Peers : Len(out[p]) <= 1

Constraint2 ==
    /\ \A p \in Peers : BagCardinality(relay[p]) <= 1

Constraint3 ==
    /\ \A p \in Peers : BagCardinality(own[p]) <= 1

Constraint4 ==
    /\ \A p \in Peers : BagCardinality(n[p]) <= 1
====
