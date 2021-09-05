-------------------------- MODULE AB_ql3 -------------------------
EXTENDS AB

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

Constraint_atmost3messages ==
    /\ Len(AtoB) =< 3
    /\ Len(BtoA) =< 3

=============================================================================
