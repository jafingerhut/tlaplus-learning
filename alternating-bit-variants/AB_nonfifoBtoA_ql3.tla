-------------------------- MODULE AB_nonfifoBtoA_ql3 -------------------------
EXTENDS AB_nonfifoBtoA, FiniteSets

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

Constraint_atmost3messages ==
    /\ Len(AtoB) =< 3
    /\ Cardinality(BtoA) =< 3

=============================================================================
