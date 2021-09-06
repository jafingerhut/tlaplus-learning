-------------------------- MODULE ABQ_nonfifo_ql -------------------------
EXTENDS ABQ_nonfifo, FiniteSets

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

Constraint_atmost3messages ==
    /\ Len(AWait) =< 1
    /\ Len(AAcked) =< 3
    /\ Len(BRcvd) =< 4
    /\ Cardinality(AtoB) =< 3
    /\ Cardinality(BtoA) =< 3

=============================================================================
