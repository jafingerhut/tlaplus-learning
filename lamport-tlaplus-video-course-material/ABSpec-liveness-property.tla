(*
ABspec-liveness-property.tla from Leslie Lamport's TLA+ Course,
Lecture 9, Part 1

https://www.youtube.com/watch?v=YA3fAzqhwJU
"Lamport TLA+ Course Lecture 9: The Alternating Bit Protocol Part 1: The High Level Spec (HD)"
*)

\A v \in Data \X {0,1} : (AVar = v) ~> (BVar = v)
