-------------------------- MODULE AB_nonfifo_ql3 -------------------------
EXTENDS AB_nonfifo, FiniteSets

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

Constraint_atmost3messages ==
    /\ Cardinality(AtoB) =< 3
    /\ Cardinality(BtoA) =< 3

=============================================================================
