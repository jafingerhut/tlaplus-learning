------------------------------- MODULE Remove -------------------------------
(*
Remove.tla from Leslie Lamport's TLA+ Course, Lecture 9, Part 1

https://www.youtube.com/watch?v=YA3fAzqhwJU
"Lamport TLA+ Course Lecture 9: The Alternating Bit Protocol Part 1: The High Level Spec (HD)"
*)

EXTENDS Integers, Sequences

Remove(i, seq) ==
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j]
                                      ELSE seq[j+1]]

=============================================================================
\* Modification History
\* Last modified Fri Sep 03 19:22:58 PDT 2021 by andy
\* Created Fri Sep 03 19:22:36 PDT 2021 by andy
