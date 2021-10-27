import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 
(2) Provide a formal proof of the proposition.
(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:
If there's a function f that maps every α value to a β value, 
for all a of type α, applying the predicate p to a will 
imply the predicate q to the function f applied to a. Thus, for
every a of type α that exists,  b of type β exists.
-/


-- Give your formal proof here
begin
  assume A B,
    cases A with alpToBeta a2,
    cases B with alpha b2,
    have a3:= a2 alpha,
    have a4:= a3 b2,
    apply exists.intro (alpToBeta alpha),
    exact a4,
end

/-
Assume that thee exists such a function that maps each α to a β for all 
'a' of type α such that the predicate p applied to a implies predicate
q applied to the outcome of the function mapping the given 'a'.
Assume that for each a of type α where p is a predicate of a.
Next, we can solve the cases of both assumptions
Applying the first assumption to a proof of α gets us a implication that p applied
to α will give q applied to β. We can get a proof of q applied to β by applying
the previous implication to p applied to α . Then if we apply the introduction
rule for exists using β we got we can solve the proposition.
-/

