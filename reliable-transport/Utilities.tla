------------------------- MODULE Utilities ------------------------
EXTENDS Integers, Sequences, Bags

(*************************************************************************)
(* If S is a set of numbers, then this defines Maximum(S) to be the      *)
(* maximum of those numbers, or -1 if S is empty.                        *)
(*************************************************************************)
Maximum(S) ==
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n \geq m

RECURSIVE SeqToBag(_)
SeqToBag(S) == IF S = << >>
                 THEN EmptyBag
                 ELSE SeqToBag(Tail(S)) \oplus SetToBag({Head(S)})

CopiesInSet(B) == {CopiesIn(e, B): e \in BagToSet(B)}

BagMaxDuplicates(B) == IF B = EmptyBag
                         THEN 0
                         ELSE Maximum(CopiesInSet(B))

=============================================================================
