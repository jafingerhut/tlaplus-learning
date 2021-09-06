----------------------------- MODULE ABSpec2_ql ------------------------------
EXTENDS ABSpec2

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

Constraint_atmost3messages ==
    /\ Len(AWait) =< 1
    /\ Len(AAcked) =< 3
    /\ Len(BRcvd) =< 4

=============================================================================
