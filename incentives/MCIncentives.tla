---- MODULE MCIncentivesR ----
EXTENDS IncentivesR

Constraint ==
    /\ \A p \in Peers : BagCardinality(b_in0[p]) <= 2

Constraint1 ==
    /\ \A p \in Peers : Len(q_out[p]) <= 2

Constraint2 ==
    /\ \A p \in Peers : Len(relaytable[p]) <= 2
====
