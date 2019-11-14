---- MODULE SeqUtils ----
EXTENDS Sequences

SeqFilter(seq, Op(_)) == SelectSeq(seq, Op)

SeqMap(seq, Op(_)) == [x \in DOMAIN seq |-> Op(seq[x])]

====
