----------------------------- MODULE GBN_ql ------------------------------
EXTENDS GBN

\* Using only 2 elements in Data_value instead of 3 significantly
\* reduces the number of states that TLC needs to evaluate.
CONSTANTS d1, d2

Data_value == {d1, d2}

Constraint_ql ==
    /\ Len(AMsgs) =< 6
    /\ Len(BMsgs) =< 6
    /\ Len(AWait) =< 1
    /\ Len(AtoB) =< 3
    /\ Len(BtoA) =< 3

NotReallyInvariant == ~ /\ Len(BMsgs) > 4
                        /\ BMsgs[1] /= BMsgs[2]
                        /\ BMsgs[2] /= BMsgs[3]

=============================================================================
