----------------------------- MODULE AB_fifo_ql ------------------------------
EXTENDS AB_fifo

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

Constraint_ql ==
    /\ Len(AMsgs) =< 5
    /\ Len(AWait) =< 1
    /\ ChannelNumMsgs(AtoB) =< 3
    /\ ChannelNumMsgs(BtoA) =< 3

NotReallyInvariant == ~ /\ Len(BMsgs) > 4
                        /\ BMsgs[1] /= BMsgs[2]
                        /\ BMsgs[2] /= BMsgs[3]
                        /\ BMsgs[1] /= BMsgs[3]

=============================================================================
