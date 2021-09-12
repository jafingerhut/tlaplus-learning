------------------------- MODULE ChannelNonFIFO_eval ------------------------
EXTENDS Utilities, Sequences

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

B0 == SeqToBag(<< >>)
B1 == SeqToBag(<< d1, d2, d1, d1 >>)
B2 == SeqToBag(<< d1, d2, d1, d2, d3 >>)

ASSUME PrintT(<<"eval B0:", B0>>)
ASSUME PrintT(<<"eval CopiesInSet(B0):", CopiesInSet(B0)>>)
ASSUME PrintT(<<"eval BagMaxDuplicates(B0):", BagMaxDuplicates(B0)>>)

ASSUME PrintT(<<"eval B1:", B1>>)
ASSUME PrintT(<<"eval CopiesInSet(B1):", CopiesInSet(B1)>>)
ASSUME PrintT(<<"eval BagMaxDuplicates(B1):", BagMaxDuplicates(B1)>>)

ASSUME PrintT(<<"eval B2:", B2>>)
ASSUME PrintT(<<"eval CopiesInSet(B2):", CopiesInSet(B2)>>)
ASSUME PrintT(<<"eval BagMaxDuplicates(B2):", BagMaxDuplicates(B2)>>)

=============================================================================
