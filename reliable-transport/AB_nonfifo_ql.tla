-------------------------- MODULE AB_nonfifo_ql -------------------------
EXTENDS AB_nonfifo

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

Constraint_ql ==
    /\ Len(AMsgs) =< 5
    /\ Len(AWait) =< 1
    /\ ChannelNumMsgs(AtoB) =< 3
    /\ ChannelNumMsgs(BtoA) =< 3

=============================================================================
