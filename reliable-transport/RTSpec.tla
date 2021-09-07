------------------------------ MODULE RTSpec --------------------------------
(*

This is intended to be a simple specification for the high level goal
of doing reliable transport of a sequence of data messages from a
sender A to a receiver B, meaning that each message is delivered at
most once, in order, with no duplicates.  Thus the receiver's state
can be represented as a sequence of data messages received, and it
must always be a prefix of the sequence of messages intended by the
sender, where sequence s1 is a prefix of sequence s2 is also true if
the two sequences are equal.

*)

EXTENDS Naturals, Sequences

CONSTANT Data  \* The set of all possible data values.

VARIABLES AMsgs,  \* The sequence of values A wants to send to B
          BMsgs   \* The sequence of values B has received so far

TypeOK == /\ AMsgs \in Seq(Data)
          /\ BMsgs \in Seq(Data)

vars == << AMsgs, BMsgs >>

Init == /\ AMsgs = << >>
        /\ BMsgs = << >>

AWrite(d) ==
    /\ d \in Data
    /\ AMsgs' = Append(AMsgs, d)
    /\ UNCHANGED <<BMsgs>>

(* If there is a message A has produced that B has not received yet, B *)
(* receives it. *)
B == /\ Len(BMsgs) < Len(AMsgs)
     /\ BMsgs' = Append(BMsgs, AMsgs[Len(BMsgs)+1])
     /\ UNCHANGED <<AMsgs>>

Next ==
    \/ \E d \in Data: AWrite(d)
    \/ B

Spec == Init /\ [][Next]_vars

SeqPrefix(s1, s2) ==
    /\ Len(s1) =< Len(s2)
    /\ \A i \in 1..Len(s1): s1[i] = s2[i]

Inv == SeqPrefix(BMsgs, AMsgs)

FairSpec == Spec /\ WF_vars(Next)

=============================================================================
