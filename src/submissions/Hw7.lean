import data.set
import  tactic.ring

namespace relation

-- PRELIMINARY SETUP

--GROUP: Sinan Seslikaya ss6gw and Alex Fetea pvn5nv

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric reflexive,
  assume prop prop1 prop2,
  cases prop with beta t,
  have prop3:= prop2 beta,
  have prop4:= prop1 prop3,
  contradiction,
end
/- 
First, we begin by unfolding the asymmetric and reflexive
and assign each of the propositions names. We then do case
analysis on the exists statement, giving us a proof of beta.
Next we apply the second proposition to beta, giving us a proof
of the relation between beta and beta. Now we apply the first
proposition to the relation between beta and beta, giving us a
proof that their is not a relation between beta and beta. This
gives us a contradiction, or a proof of false.

The proposition would not be true if b was not inhabited, because
an empty set would be a counterexample
-/






/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example :¬symmetric r →transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold symmetric transitive reflexive asymmetric,
  intros s t i a,
  apply not.intro s,
  assume x y,
  assume rxy,
  have rxx:= i x,
  have nrxx:= a rxx,
  contradiction,
end
/-
The initial conjecture that a relation that is transitive and reflexive is
also asymmetric is not true. A counter example to this would be a set
in which every element is only related to itself. this would be transitive
reflexive and antisymmetric.
-/



/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  intros s s1 s2 prop1 prop2 s12 s21,
  apply set.ext,
  assume beta,
  apply iff.intro,
  assume bs2,
  have a:= s12 bs2,
  exact a,
  assume bs1,
  have b:= s21 bs1,
  exact b,
end
/-
First we start by assigning variable names to all of the propositions.
We then apply set.ext, which breaks down the statement of equality. We
then apply the intro rule for if and only if, in order to seperate the
biimplication. We then apply the proposition that s1 is a subset of s2
to beta is a subset of s1, giving us a proof that beta is a subset of
s2. Then we apply the proposition that s2 is a subset of s1 to beta 
is a subset of s1, giving us a proposition that beta is a subset of s1.
-/


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro n,
  ring,
end
/-
First we assume the variable n and unfold the divides statement. Next,
we apply the intro rule for exists to n, giving us a proof of n = n * 1.
Finally, we use the ring function to simplify.
-/

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end
/-
First we assume the variable n and unfold the divides statement. Next,
we apply the intro rule for exists to 1, giving us a proof of n = n * 1.
Finally, we use the ring function to simplify.
-/

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  assume n,
  unfold reflexive divides,
  apply exists.intro 1,
  ring,
end 
/-
First we assume the variable n and unfold the reflexive divides statement.
Next, we apply the intro rule for exists to 1, giving us a proof of 
n = n * 1. Finally, we use the ring function to simplify.
-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume x y z prop prop1,
  apply exists.intro 1,
  ring,

  cases prop with k c,
  cases prop1 with k1 d,
  
  have k2: k = 1 :=sorry,
  have k3: k1 = 1 :=sorry,

  rw d,
  rw c,
  ring,

  rw k2,
  rw k3,
  ring,
end 
/-
First we unfold the transitive divides statement. Next, we apply the intro
rule for exists to 1. We now need to prove that z=x. We do cases on the
first prop, giving us a proof of y = k * x. We then do cases on the second
prop, giving us a proof of z = k1 * y. We then assign values of 1 to both k
and k1 and rewrite the proofs, giving us a proof of y=x and z=y. We then 
rewrite these proofs to give us a proof that z=x.
-/



/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/
example : symmetric divides :=
begin
  
  unfold symmetric divides,
  assume x y a,
  apply exists.intro 1,
  ring,
  cases a with k prop,
  have k1: k = 1 :=sorry,
  rw prop,
  rw k1,
  ring,
end 
/-
First we unfold the transitive divides statement. We then apply the intro
rule for exists to 1. We now have to prove that x=y. Next, we conduct cases
on a, giving us a proof that y=k*x. Next we create a proof that k=1, and
rewrite the first proof, giving us a proof that x=y. 
-/



/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin  
  unfold anti_symmetric divides,
  assume x y a b,
  cases a with k yeq,
  have k1: k=1:=sorry,
  rw yeq,
  rw k1,
  ring,
end
/-
First we unfold the asymmetric divides statement. We then conduce cases on
the first proposition, giving us a proof that y = k*x. Next we create a proof
that k=1, and rewrite the first proof, giving us a proof that x=y.
-/



/- #5
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume prop x rxx,
  have nrxx:= prop rxx,
  contradiction
end
/-
First we unfold the asymmetric irreflexive statement. We get a proof of
¬rxx by apply the asymmetric relation to rxx. We then have a proof of
false.
-/



-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  assume prop prop1 x y rxy ryx,
  have rxx:= prop1 rxy ryx,
  have nrxx:= prop x,
  contradiction,
end
/-
First we unfold the irreflexive transitive asymmetric statement. We get a
proof of rxx by applying the transitive relation to rxy and ryx. We then 
get a proof of ¬rxx by applying the irreflexive relation to x. We now
have a proof of flase by contraction.
-/

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume t s i,
  apply not.intro s,
  assume x y,
  assume rxy,
end
/-
We don't believe this problem is provable; reflexivity describes an object's
relation with itself. A counterexample would be a completely empty set except
element A is related to element B. This would be be ¬ symmetric transitive and
irreflexive.
-/


end relation