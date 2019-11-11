---- MODULE UnreliableChannel ----
EXTENDS Naturals, Sequences

\* The action of loosing a message from queue q.
\* Leaves every variable unchanged except msgQ and ackQ
Lose(q) ==
    /\ q # << >>            \* Enabled iff q is not empty
    /\ \E i \in 1..Len(q) : \* For some i, remove the ith message from q.
        q' = [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]

\* The action of duplicating a message from queue q.
Dup(q) ==
    /\ q # << >>            \* Enabled iff q is not empty
    /\ \E i \in 1..Len(q) : \* For some i, append it to the q.
        q' = Append(q, q[i])

\* The action of reordering a message in queue q.
Mix(q) ==
    /\ q # << >>            \* Enabled iff q is not empty
    /\ \E i, j \in 1..Len(q) : \* For some i, j swap.
        q' = [q EXCEPT ![i] = q[j], ![j] = q[i]]

\* A failure action which can be one of Lose, Dup or Mix.
Fail(q) == Lose(q) \/ Dup(q) \/ Mix(q)

====
