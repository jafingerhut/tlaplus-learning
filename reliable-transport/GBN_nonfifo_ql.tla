------------------------- MODULE GBN_nonfifo_ql --------------------------
EXTENDS GBN_nonfifo

\* Using only 2 elements in Data_value instead of 3 significantly
\* reduces the number of states that TLC needs to evaluate.
CONSTANTS d1, d2

Data_value == {d1, d2}

Constraint_ql ==
    /\ Len(AMsgs) =< 6
    /\ Len(BMsgs) =< 6
    /\ Len(AWait) =< 1
    /\ ChannelNumMsgs(AtoB) =< 3
    /\ ChannelNumMsgs(BtoA) =< 3
    /\ ChannelMaxDuplicateMsgs(AtoB) =< 2
    /\ ChannelMaxDuplicateMsgs(BtoA) =< 2

NotReallyInvariant == ~ /\ Len(BMsgs) > 4
                        /\ BMsgs[1] /= BMsgs[2]
                        /\ BMsgs[2] /= BMsgs[3]

=============================================================================
