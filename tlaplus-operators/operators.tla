---- MODULE operators ----
EXTENDS TLC, Integers, Sequences, FiniteSets, Bags

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Selected syntax and operators">>)
ASSUME PrintT(<<"(introduced 'out of order' here because they are so useful in">>)
ASSUME PrintT(<<"creating examples for evaluation and printing)">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"set of natural numbers in a range: 0..2  ", 0..2>>)
ASSUME PrintT(<<"cross product of sets results in a set of tuples: (0..2) \\X (3..5)  ", (0..2) \X (3..5)>>)

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.1 Boolean Operators">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"BOOLEAN is the set of boolean values  ", BOOLEAN>>)
ASSUME PrintT(<<"logical AND, conjunction: TRUE /\\ TRUE  ", TRUE /\ TRUE>>)
ASSUME PrintT(<<"logical OR,  disjunction: FALSE \\/ FALSE  ", FALSE \/ FALSE>>)
ASSUME PrintT(<<"logical NOT, negation:    ~FALSE, \\lnot FALSE, \\neg FALSE  ", ~FALSE, \lnot FALSE, \neg FALSE>>)
ASSUME PrintT(<<"logical IMPLIES, implication: TRUE => FALSE  ", TRUE => FALSE>>)
ASSUME PrintT(<<"logical EQUIVALENCE: FALSE <=> FALSE, FALSE \\equiv FALSE  ", FALSE <=> FALSE, FALSE \equiv FALSE>>)

ASSUME PrintT(<<"---------- unbounded quantification ----------">>)
ASSUME PrintT(<<"unbounded universal quantifier, for all: \\A x: x > 0  ", "tlc gives an error if it attempts to evaluate an unbounded \\A for printing">>)
ASSUME PrintT(<<"unbounded existential quantifier, there exists: \\E x: x > 0  ", "tlc gives an error if it attempts to evaluate an unbounded \\E for printing">>)

ASSUME PrintT(<<"---------- bounded quantification ----------">>)
ASSUME PrintT(<<"bounded universal quantifier, for all: \\A x \\in Nat: x > 0  ", "tlc gives error 'encountered a non-enumerable quantifier bound Nat' when attempting to evalute such an expression for printing">>)
ASSUME PrintT(<<"bounded existential quantifier, there exists: \\E x \\in Nat: x > 0  ", "tlc gives error 'encountered a non-enumerable quantifier bound Nat' when attempting to evalute such an expression for printing">>)

ASSUME PrintT(<<"bounded universal quantifier, for all:">>)
ASSUME PrintT(<<"  \\A x \\in 0..5: x > 0  ", \A x \in 0..5: x > 0>>)
ASSUME PrintT(<<"bounded existential quantifier, there exists:">>)
ASSUME PrintT(<<"  \\E x \\in 0..5: x > 0  ", \E x \in 0..5: x > 0>>)
ASSUME PrintT(<<"bounded universal quantifier, for all, over multiple variables:">>)
ASSUME PrintT(<<"  \\A x \\in 0..5, y \\in 0..5: x + y > 0  ", \A x \in 0..5, y \in 0..5: x + y > 0>>)
ASSUME PrintT(<<"bounded existential quantifier, there exists, over multiple variables:">>)
ASSUME PrintT(<<"  \\E x \\in 0..5, y \\in 0..5: x + y > 0  ", \E x \in 0..5, y \in 0..5: x + y > 0>>)

\* TBD: See spec book p. 293 quantification over tuples.  Write example.

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.2 The Choose Operator">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"TODO">>)

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.4 Conditional Constructs">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"TODO">>)

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.5 The Let/In Construct">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"TODO">>)

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.6 The Operators of Set Theory">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"enumerate elements of a set:">>)
ASSUME PrintT(<<"  {1, 5, 8}:", {1,5,8}>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"all x in set S such that condition p is TRUE {x \\in S: p}:">>)
ASSUME PrintT(<<"  {x \\in Nat: (x % 3) = 1}:", "tlc gives error 'Attempted to enumerate <expression> when S: Nat is not enumerable' when attempting to evalute such an expression for printing">>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"all x in set S such that condition p is TRUE {x \\in S: p}:">>)
ASSUME PrintT(<<"  {x \\in 0..10: (x % 3) = 1}:", {x \in 0..10: (x % 3) = 1}>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"all tuples in set S such that condition p is TRUE {<<a, b>> \\in set_of_tuples: p}:">>)
ASSUME PrintT(<<"  {<<a, b>> \\in (0..5) \\X (3..7) : a > b}:", {<<a, b>> \in (0..5) \X (3..7) : a > b}>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"all values of expression e (usually containing x) such that x is in set S {e: x \\in S}:">>)
ASSUME PrintT(<<"  {7 * x: x \\in 0..10}:", {7 * x: x \in 0..10}>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"all values of expression e such that multiple variables are in their respective sets {e: x,y \\in S, z \\in T}:">>)
ASSUME PrintT(<<"  {x+y-z: x,y \\in 10..12, z \\in 4..5}:", {x+y-z: x,y \in 10..12, z \in 4..6}>>)
ASSUME PrintT(<<"  {<<x, y-z>>: x,y \\in 10..12, z \\in 4..5}:", {<<x, y-z>>: x,y \in 10..12, z \in 4..6}>>)

\* todo \in \notin = /= #
\* todo UNION SUBSET
\* todo \subseteq
\* todo \supseteq
\* todo \cup or \union
\* todo \cap or \intersect
\* todo \ (set difference)

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.7 Functions">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"The set of all functions with domain S and range T: [S -> T]">>)
ASSUME PrintT(<<"  [5..7 -> BOOLEAN  ", [5..7 -> BOOLEAN]>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"One function (unnamed) with domain S and value given by expression e: [x \\in S |-> e]">>)
ASSUME PrintT(<<"  [x \\in 5..7 |-> 2*x-4]", [x \in 5..7 |-> 2*x-4]>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"You can define a function with a name 'fcn' as follows:">>)
ASSUME PrintT(<<"  fcn[x \\in S] == e">>)
ASSUME PrintT(<<"Example: fn1[x \\in 0..3] == IF x = 3 THEN 0 ELSE x+1">>)
fn1[x \in 0..3] == IF x = 3 THEN 0 ELSE x+1
ASSUME PrintT(<<"  fn1  ", fn1>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"You can define a recursive function by using the function's">>)
ASSUME PrintT(<<"name in its definition.">>)
ASSUME PrintT(<<"Example: fib[x \\in 0..8] == IF x < 2 THEN 1 ELSE fib[x-1] + fib[x-2]">>)
fib[x \in 0..8] == IF x < 2 THEN 1 ELSE fib[x-1] + fib[x-2]
ASSUME PrintT(<<"  fib  ", fib>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"EXCEPT is useful for defining new functions that are the same">>)
ASSUME PrintT(<<"as an existing function, with one or several exceptions.">>)
ASSUME PrintT(<<"  [fn1 EXCEPT ![1] = 18]  ", [fn1 EXCEPT ![1] = 18]>>)
ASSUME PrintT(<<"  [fn1 EXCEPT ![1] = 18, ![3] = 5]  ", [fn1 EXCEPT ![1] = 18, ![3] = 5]>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"TLA+ functions of multiple arguments have domain that are sets">>)
ASSUME PrintT(<<"of tuples: f[x,y,z] is an abbreviation for f[<<x,y,z>>].">>)
ASSUME PrintT(<<"The following are two ways to write the same function:">>)
ASSUME PrintT(<<"  [a \\in 0..2, b \\in 4..5 |-> b-a]", [a \in 0..2, b \in 4..5 |-> b-a]>>)
ASSUME PrintT(<<"  [<<a, b>> \\in (0..2) \\X (4..5) |-> b-a]", [<<a, b>> \in (0..2) \X (4..5) |-> b-a]>>)


ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.8 Records">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"In TLA+ records are a bit like C structs or the fields of Java objects.">>)
ASSUME PrintT(<<"They are simply a different syntax for a function from strings naming">>)
ASSUME PrintT(<<"the fields, to the values of those fields.">>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"The set of all records with field name">>)
ASSUME PrintT(<<"  f1 that can take on value in set S1={0,1,2},">>)
ASSUME PrintT(<<"  f2 that can take on value in set S2=BOOLEAN,">>)
ASSUME PrintT(<<"  f3 that can take on value in set S3={\"a\", \"b\"},">>)
ASSUME PrintT(<<"is written:">>)
ASSUME PrintT(<<"  [f1: {4,7}, f2:BOOLEAN, f3:{\"a\", \"b\"}]  ",
                   [f1: {4,7}, f2:BOOLEAN, f3:{"a", "b"}]>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"One record in that set can be written this way:">>)
ASSUME PrintT(<<"  [f1 |-> 7, f2 |-> FALSE, f3 |-> \"a\"]  ",
                   [f1 |-> 7, f2 |-> FALSE, f3 |-> "a"]>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"The EXCEPT expression works for records similarly to how it works for">>)
ASSUME PrintT(<<"with only a slight difference in syntax:">>)
rec1 == [f1 |-> 7, f2 |-> FALSE, f3 |-> "a"]
ASSUME PrintT(<<"  rec1 == [f1 |-> 7, f2 |-> FALSE, f3:\"a\"]">>)
ASSUME PrintT(<<"  [rec1 EXCEPT !.f2 = TRUE]  ",
                   [rec1 EXCEPT !.f2 = TRUE]>>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.9 Tuples">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"The set of all n-tuples where">>)
ASSUME PrintT(<<"  tuple element number 1 is in the set S1={0,1,2},">>)
ASSUME PrintT(<<"  tuple element number 2 is in the set S2=BOOLEAN,">>)
ASSUME PrintT(<<"  tuple element number 3 is in the set S3={\"a\", \"b\"},">>)
ASSUME PrintT(<<"is written:">>)
ASSUME PrintT(<<"  {4,7} \\X BOOLEAN \\X {\"a\", \"b\"}  ",
                   {4,7} \X BOOLEAN \X {"a", "b"}>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"One tuple in that set can be written this way:">>)
ASSUME PrintT(<<"  <<7, FALSE, \"a\">>  ",
                   <<7, FALSE, "a">>>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"An N-tuple in TLA+ is equivalent to a function with domain 1..N">>)
tup1 == <<7, FALSE, "a">>
ASSUME PrintT(<<"  tup1 == <<7, FALSE, \"a\">>">>)
fnt1 == [i \in 1..3 |-> IF i=1 THEN 7 ELSE IF i=2 THEN FALSE ELSE "a"]
ASSUME PrintT(<<"  fnt1 == [i \\in 1..3 |-> IF i=1 THEN 7 ELSE IF i=2 THEN FALSE ELSE \"a\"]">>)
ASSUME PrintT(<<"  tup1 = fnt1  ",
                   tup1 = fnt1>>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"The 0-tuple is written << >>">>)
ASSUME PrintT(<<>>)
ASSUME PrintT(<<"The standard Sequences module uses n-tuples to represent">>)
ASSUME PrintT(<<"sequences of length n">>)

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 18.1 Module Sequences">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"The set of all finite sequences with elements in S:">>)
ASSUME PrintT(<<"  Seq(S)">>)
ASSUME PrintT(<<"The length of sequence s:">>)
ASSUME PrintT(<<"  Len(s)">>)
seq1 == <<10, 20, 30>>
ASSUME PrintT(<<"  seq1 == <<10, 20, 30>>">>)
seq2 == <<"a", "b">>
ASSUME PrintT(<<"  seq2 == <<\"a\", \"b\">>">>)
ASSUME PrintT(<<"  Len(seq1)  ", Len(seq1)>>)
ASSUME PrintT(<<"The concatenation of sequences s1 followed by s2:">>)
ASSUME PrintT(<<"  s1 \\o s2      alternately: s1 \\circ s2">>)
ASSUME PrintT(<<"  seq1 \\o seq2  ", seq1 \o seq2>>)
ASSUME PrintT(<<"The sequence obtained by appending element e after the end of sequence s:">>)
ASSUME PrintT(<<"  Append(s, e)">>)
ASSUME PrintT(<<"  Append(seq1, 42)  ", Append(seq1, 42)>>)
ASSUME PrintT(<<"The first element of sequence s:">>)
ASSUME PrintT(<<"  Head(s)">>)
ASSUME PrintT(<<"  Head(seq2)", Head(seq2)>>)
ASSUME PrintT(<<"The sequence of all but the he first element of sequence s:">>)
ASSUME PrintT(<<"  Tail(s)">>)
ASSUME PrintT(<<"  Tail(seq2)", Tail(seq2)>>)
ASSUME PrintT(<<"  Tail(Tail(seq2))", Tail(Tail(seq2))>>)
ASSUME PrintT(<<"The sequence starting with element at index m, up to element at index n, inclusive:">>)
ASSUME PrintT(<<"  SubSeq(s, m, n)">>)
ASSUME PrintT(<<"  SubSeq(seq1, 3, 3)", SubSeq(seq1, 3, 3)>>)
ASSUME PrintT(<<"The subsequence of s containing all elements e such that Test(e) is TRUE:">>)
ASSUME PrintT(<<"  SelectSeq(s, Test(_))">>)
MultipleOf4(n) == (n % 4) = 0
ASSUME PrintT(<<"  MultipleOf4(n) == (n % 4) = 0">>)
ASSUME PrintT(<<"  SelectSeq(seq1, MultipleOf4)", SelectSeq(seq1, MultipleOf4)>>)

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 18.2 Module FiniteSets">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Determine whether a set S is finite:">>)
ASSUME PrintT(<<"  IsFiniteSet(S)">>)
ASSUME PrintT(<<"  IsFiniteSet({2,4,6})",
                   IsFiniteSet({2,4,6})>>)
ASSUME PrintT(<<"  IsFiniteSet(Nat)",
                   IsFiniteSet(Nat)>>)
ASSUME PrintT(<<"The cardinality of a set is defined only for finite sets:">>)
ASSUME PrintT(<<"  Cardinality(S)">>)
ASSUME PrintT(<<"  Cardinality({2,4,6})",
                   Cardinality({2,4,6})>>)
ASSUME PrintT(<<"  Cardinality(Nat)",
                "tlc gives error 'Attempted to compute cardinality of the value Nat' if i attempts to evaluate this.">>)

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 18.3 Module Bags">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"The bag that contains one copy of every element of the set S">>)
ASSUME PrintT(<<"  SetToBag(S)">>)
ASSUME PrintT(<<"  SetToBag({1,2,4})",
                   SetToBag({1,2,4})>>)
ASSUME PrintT(<<"  SetToBag({\"a\",\"c\",\"c\"})",
                   SetToBag({"a","b","c"})>>)
ASSUME PrintT(<<"True iff B is a bag:">>)
ASSUME PrintT(<<"  IsABag(B)">>)
ASSUME PrintT(<<"  IsABag(SetToBag({1,2,3}))",
                   IsABag(SetToBag({1,2,3}))>>)
ASSUME PrintT(<<"  IsABag({1,2,3})",
                   IsABag({1,2,3})>>)
ASSUME PrintT(<<"The union of bags B1 and B2">>)
ASSUME PrintT(<<"  B1 (+) B2     alternately:   B1 \\oplus B2">>)
bag1 == SetToBag({1,2,4})
ASSUME PrintT(<<"  bag1 == SetToBag({1,2,4})">>)
ASSUME PrintT(<<"  bag1", bag1>>)
bag2 == SetToBag({  2,4,5})
ASSUME PrintT(<<"  bag2 == SetToBag({  2,4,5})">>)
ASSUME PrintT(<<"  bag2", bag2>>)
bag3 == bag1 \oplus bag2
ASSUME PrintT(<<"  bag3 == bag1 \\oplus bag2">>)
ASSUME PrintT(<<"  bag3", bag3>>)
bag4 == bag3 \oplus bag3
ASSUME PrintT(<<"  bag4 == bag3 \\oplus bag3">>)
ASSUME PrintT(<<"  bag4", bag4>>)
bag5 == SetToBag({      5,6,7})
ASSUME PrintT(<<"  bag5 == SetToBag({      5,6,7})">>)
ASSUME PrintT(<<"  bag5", bag5>>)
ASSUME PrintT(<<"The set of elements that have at least one copy in bag B">>)
ASSUME PrintT(<<"  BagToSet(B)">>)
ASSUME PrintT(<<"  BagToSet(bag4)", BagToSet(bag4)>>)
ASSUME PrintT(<<"The \\in operator for bags">>)
ASSUME PrintT(<<"  BagIn(e, B)">>)
ASSUME PrintT(<<"  BagIn(1, bag4)", BagIn(1, bag4)>>)
ASSUME PrintT(<<"  BagIn(8, bag4)", BagIn(8, bag4)>>)
ASSUME PrintT(<<"The empty bag">>)
ASSUME PrintT(<<"  EmptyBag">>)
ASSUME PrintT(<<"The number of copies of e in bag B">>)
ASSUME PrintT(<<"  CopiesIn(e, B)">>)
ASSUME PrintT(<<"  CopiesIn(1, bag4)", CopiesIn(1, bag4)>>)
ASSUME PrintT(<<"  CopiesIn(8, bag4)", CopiesIn(8, bag4)>>)
ASSUME PrintT(<<"The bag B1 with the elements of B2 removed">>)
ASSUME PrintT(<<"  B1 (-) B2     alternately:   B1 \\ominus B2">>)
ASSUME PrintT(<<"  bag4 \\ominus bag5", bag4 \ominus bag5>>)
ASSUME PrintT(<<"The bag union of all elements of the set S of bags">>)
ASSUME PrintT(<<"  BagUnion(S)">>)
\* TODO: example
ASSUME PrintT(<<"The subset operator for bags">>)
ASSUME PrintT(<<"  B1 \\sqsubseteq B2">>)
ASSUME PrintT(<<"  bag1 \\sqsubseteq bag4",
                   bag1 \sqsubseteq bag4>>)
ASSUME PrintT(<<"  bag1 \\sqsubseteq bag5",
                   bag1 \sqsubseteq bag5>>)
ASSUME PrintT(<<"The set of all subbags of bag B">>)
ASSUME PrintT(<<"  SubBag(B)">>)
\* TODO: example
ASSUME PrintT(<<"The bag analog of the set {F(x): x \\in B} for a set B">>)
ASSUME PrintT(<<"  BagOfAll(F(_), B)">>)
\* TODO: example
ASSUME PrintT(<<"The total number of copies of elements in bag B">>)
ASSUME PrintT(<<"  BagCardinality(B)">>)
ASSUME PrintT(<<"  BagCardinality(bag1)",
                   BagCardinality(bag1)>>)
ASSUME PrintT(<<"  BagCardinality(bag4)",
                   BagCardinality(bag4)>>)

\* TODO: Add SUBSET somewhere appropriate
\* TODO: Add set operators like union intersection difference

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 18.4 The Numbers Modules -- Naturals">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)

\* todo Nat + - * a^b
\* todo <= =< \leq
\* todo >= \geq
\* todo < >
\* todo a..b
\* todo \div  %

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.10 Strings">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"TODO">>)

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.11 Numbers">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"TODO">>)

ASSUME PrintT(<<"something:", <<0..2, 1..3>>>>)
==========================
