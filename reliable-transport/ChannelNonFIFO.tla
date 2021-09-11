--------------------------- MODULE ChannelNonFIFO --------------------------
EXTENDS Integers, Bags

EmptyChannel == EmptyBag

AllBagsOfSetUpToNCopies(s, N) ==
    UNION {[SB -> 1..N]: SB \in SUBSET s}

\* 10 was chosen fairly arbitrarily here as probably large enough to
\* catch any errors in the protocol.  I do not know if there is a good
\* way in TLA+ to specify a Bag that can have an arbitrarily large
\* number of copies of each element.  Even if I knew how, I am not
\* sure whether I would want to use such a formula for this purpose,
\* given the possible explosion in number of possible reachable
\* states.
ChannelType(MessageType) == AllBagsOfSetUpToNCopies(MessageType, 10)

ChannelAfterSendMsg(C, M) == C \oplus SetToBag({M})

\* Any message in the bag can be received.
SetOfReceivableMessages(C) == BagToSet(C)

ChannelAfterReceiveMsg(C, M) == C \ominus SetToBag({M})

ChannelLoseMsg(C) == \E M \in BagToSet(C):
                         C' = C \ominus SetToBag({M})

ChannelNumMsgs(C) == BagCardinality(C)
=============================================================================
