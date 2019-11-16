---- MODULE MCIncentivesR ----
EXTENDS IncentivesR

Constraint ==
    /\ \A p \in Peers : /\ Len(q_in[p]) <= 2
                        /\ Len(q_out[p]) <= 2
                        /\ relaytable[p] <= LoadBound

====
