------------------------------ MODULE ABSpec2 --------------------------------
(*

Model the requirements of a reliable transport / data link protocol,
as being capable of conveying a sequence of data values from sender to
receiver, such that the receiver's queue of received messages is
always a prefix of the messages sent by the sender (with equality
allowed as part of the definition of a prefix).

*)

EXTENDS Integers, Sequences

CONSTANT Data  \* The set of all possible data values.

VARIABLES AWait,  \* The sequence of values that A has not transmitted yet
          AVar,   \* The value A is currently waiting for an ack from B
          AAcked, \* The sequence of values that A has confirmed that B has received
          BVar,   \* The value most recently received at B
          BRcvd   \* The sequence of values that B has received

(***************************************************************************)
(* Type correctness means that Apend, AAcked, and BRcvd are *)
(* sequences of values, each from the set Data.                            *)
(***************************************************************************)
TypeOK ==
    /\ AWait \in Seq(Data)
    /\ AVar \in Data \X {0,1}
    /\ AAcked \in Seq(Data)
    /\ BVar \in Data \X {0,1}
    /\ BRcvd \in Seq(Data)

(***************************************************************************)
(* It's useful to define vars to be the tuple of all variables, for        *)
(* example so we can write [Next]_vars instead of [Next]_<< ...  >>        *)
(***************************************************************************)
vars == << AWait, AVar, AAcked, BVar, BRcvd >>

Init ==
    /\ AWait = << >>
    /\ AVar \in Data \X {1}
    /\ AAcked = << >>
    /\ BVar = AVar
    /\ BRcvd = << >>

(***************************************************************************)
(* When AVar = BVar, the sender can "send" an arbitrary data d item by     *)
(* setting AVar[1] to d and complementing AVar[2].  It then waits until    *)
(* the receiver "receives" the message by setting BVar to AVar before it   *)
(* can send its next message.  Sending is described by action A and        *)
(* receiving by action B.                                                  *)
(***************************************************************************)
AWrite(d) ==
    /\ d \in Data
    /\ AWait' = Append(AWait, d)
    /\ UNCHANGED <<AVar, AAcked, BVar, BRcvd>>

Asnd ==
    /\ AWait /= << >>
    /\ AVar = BVar
    /\ AVar' = <<Head(AWait), 1 - AVar[2]>>
    /\ AWait' = Tail(AWait)
    /\ AAcked' = Append(AAcked, AVar[1])
    /\ UNCHANGED <<BVar, BRcvd>>

Brcv ==
    /\ BVar /= AVar
    /\ BVar' = AVar
    /\ BRcvd' = Append(BRcvd, BVar[1])
    /\ UNCHANGED <<AWait, AVar, AAcked>>

Next ==
    \/ \E d \in Data: AWrite(d)
    \/ Asnd
    \/ Brcv

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* For understanding the spec, it's useful to define formulas that should  *)
(* be invariants and check that they are invariant.  The following         *)
(* invariant Inv asserts that, if AVar and BVar have equal second          *)
(* components, then they are equal (which by the invariance of TypeOK      *)
(* implies that they have equal first components).                         *)
(***************************************************************************)
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

AAckedOrPending == Append(AAcked, AVar[1])

SeqPrefix(s1, s2) ==
    /\ Len(s1) =< Len(s2)
    /\ \A i \in 1..Len(s1): s1[i] = s2[i]

PrefixInv == SeqPrefix(BRcvd, AAckedOrPending)

NotReallyInvariant == Len(BRcvd) =< 2

-----------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is Spec with the addition requirement that it keeps taking     *)
(* steps.                                                                  *)
(***************************************************************************)
FairSpec == Spec /\ WF_vars(Next)
=============================================================================

