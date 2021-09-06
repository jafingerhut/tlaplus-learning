-------------------------- MODULE ABQ_ql -------------------------
EXTENDS ABQ

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

Constraint_atmost3messages ==
    /\ Len(AWait) =< 1
    /\ Len(AAcked) =< 3
    /\ Len(BRcvd) =< 4
    /\ Len(AtoB) =< 3
    /\ Len(BtoA) =< 3

=============================================================================
