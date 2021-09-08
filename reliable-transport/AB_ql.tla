----------------------------- MODULE AB_ql ------------------------------
EXTENDS AB

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

Constraint_ql ==
    /\ Len(AMsgs) =< 5
    /\ Len(AWait) =< 1
    /\ Len(AtoB) =< 3
    /\ Len(BtoA) =< 3

NotReallyInvariant == ~ /\ Len(BMsgs) > 4
                        /\ BMsgs[1] /= BMsgs[2]
                        /\ BMsgs[2] /= BMsgs[3]
                        /\ BMsgs[1] /= BMsgs[3]

=============================================================================
