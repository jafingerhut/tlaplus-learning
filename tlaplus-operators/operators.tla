---- MODULE operators ----
EXTENDS TLC, Integers

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

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.8 Records">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"TODO">>)

ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"Section 16.1.9 Tuples">>)
ASSUME PrintT(<<"----------------------------------------------------------------------">>)
ASSUME PrintT(<<"TODO">>)

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
