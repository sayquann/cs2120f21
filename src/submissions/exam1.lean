/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
----------------------------------
     (pf : Q)


English:  Given props P  and Q, 
A proof that P implies Q and a proof of P
proves  Q.

-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume pq,
  assume p,
  exact pq p,
end

-- Extra credit [2 points]. Who invented this principle?

-- Aristotle

-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- If you have a proof that a proposition implies true, you have a proof of the
proposition. 

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := 
begin
  apply true.intro,
end

-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- if you have a proof of P and a proof of Q, you can have
a proof of P ∧ Q

ELIMINATION

Given the elimination rules for ∧ in both
inference rule and English language forms.
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q: Prop),  Q ∧ P → P :=
begin
  assume P Q,
  assume pq,
  apply and.elim_right pq,
end 


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- The intro rule ∀ is that it applies the following 
to any and all


ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                (pf : Q )

-- For all applies to any  and all of that value, thus if 
for  all of a type a proposition is true, given an object of
that type, the proposition is true by elimination rule

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- For a type T and a proposition Q, if pf is a  proof that all
t of type T and for proposition Q, if we proove that t is a type T,
we have a proof of Q from pf.
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
    (Lynn : Person)
    (L : KnowsLogic Lynn)
    -- (L2 : BetterComputerScientist Lynn)
  
  (∀(Lynn : Person), Lynn → BetterComputerScientist)

  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
  -- add answer here
  -- add answer here

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : (∀(Lynn : Person), Lynn → BetterComputerScientist) := _



-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → P -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 


Proof by negation is proving that the opposite to the 
proposition can be used to construct a proof of false, thus cant actually be
a proof because it is absurd. If we can prove that not of  a proposition 
leads to false that the prop itself leads to true. If we are trying to prove ¬P, 
we can try to show that P→false and thus that it P cannot be true.


Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume ¬P and show that ¬P → false.
From this derivation you can conclude ¬¬P → true.
Then you apply the rule of negation elimination
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is classically valid, and that accepting the axiom
of the classical elimination suffices to establish negation
elimination (better called double negation elimination)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (P Q : Prop), (P→Q) → (Q→P) → (P↔Q) :=
begin
  assume P Q,
  assume pq qp,
  apply iff.intro,
  exact pq,
  exact qp,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    
/-
To proove that everyone like john lennon start with that all persons can have the
attributes nice and talented and that likes is attribute that connect one person 
to another. Everyone likes a nice, talented person can be expressed as if a person
is nice that implies they are talented, than every  person likes that original person.
we can then apply  that to  johnlennon given that he is nice and talented. 

-/
example : ELJL :=
begin
 intro,
 assume p,
 assume p,
 assume pp,
 assume p1,
 assume jl,
 assume q,
 assume b,
 apply p1,
 apply and.elim_left q,
 apply and.elim_right q,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? 4
-- list the cases (informaly)
    -- red and heavy
    -- red and light
    -- blue and heavy
    -- blue and light

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop :=
  ∀ (T : Type) (x y z : T), x = y → y = z → x = z


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : ∀(P : Prop), (¬¬P → P) ↔ ¬(P ∧ ¬P) := 
begin
  assume p,
  apply iff.intro,
  --forward
  assume nnpp,
  apply not.intro,
  assume pnp,
  have p:= pnp.left,
  have np:= pnp.right,
  contradiction,
  --backward
  assume  npnp,
  assume nnp,
  cases (classical.em p), 
  exact h,
  contradiction,
end



/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
there is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop 

example :_ := _
