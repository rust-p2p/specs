---- MODULE MCIncentives ----
EXTENDS Incentives

Constraint ==
    /\ \A <<p,t>> \in Peers \X Type : BagCardinality(b_in[p,t]) <= 2

Constraint1 ==
    /\ \A p \in Peers : Len(q_out[p]) <= 2

Constraint2 ==
    /\ \A p \in Peers : Len(relaytable[p]) <= 2
====
