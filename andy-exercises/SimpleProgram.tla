--------------------------- MODULE SimpleProgram ---------------------------
(*
SimpleProgram.tla from Leslie Lamport's TLA+ Course, Lecture 3

https://www.youtube.com/watch?v=4NtHUfXlf4g
"Lamport TLA+ Course Lecture 3: Resources and Tools (HD)"
*)

EXTENDS Integers
VARIABLES i, pc   

Init == (pc = "start") /\ (i = 0)

Pick == /\ pc = "start"  
        /\ i' \in 0..1000
        /\ pc' = "middle"

Add1 == /\ pc = "middle" 
        /\ i' = i + 1
        /\ pc' = "done"  
           
Next == Pick \/ Add1

=============================================================================
\* Modification History
\* Last modified Wed Sep 01 18:58:20 PDT 2021 by andy
\* Created Wed Sep 01 18:53:04 PDT 2021 by andy
