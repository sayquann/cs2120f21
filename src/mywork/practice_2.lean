/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _   -- trick question? why?

-- false does not have an intro rule

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
    assume P, 
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. Next, use the elimination rule for or to show that p → p. To finish it off,
use the intro rule of or to show that p → p, QED
-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
    assume P,
  apply iff.intro _ _,
    assume prop,
    apply and.elim prop,
      assume p,
    assume p,
    exact p,
    assume prop,
  apply and.intro _ _,
  apply prop,
  apply prop,
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. Next,  use the elimination rule for  and  to show that P ∧  P → P.
Next, we use the introduction rule for and to prove P ∧ P. QED
-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P,
  assume Q,

  apply iff.intro _ _,
  assume A,
  
  apply or.elim A,
  assume p,
  apply  or.intro_right,
  exact p,

  assume B,
  apply or.intro_left,
  apply B,

  assume q,
  apply or.elim q,
  assume h,
  apply or.intro_right,
  exact h,

  assume j,
  apply or.intro_left,
  exact j,
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. Next,  use the elimination rule for or to see that we need to prove 
P → Q ∧ P and Q → Q ∧ P. Next, use the introduction rule for or to show that 
P → Q ∧ P and Q → Q ∧ P. Repeat process to solve for backwards. QED 
-/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _ ,
  assume A,
  
  apply and.elim  A,
  assume p,
  assume q,
  apply and.intro,
  exact q,
  exact p,

  assume B,
  apply and.elim B,
  assume q p,
  apply and.intro,
  exact p, 
  exact q,
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. Use the and elimination rule to show that P ∧ Q → Q ∧ P is equivalent to
P → Q → Q ∧ P. Use the introduction rule  for and to prove the latter statement. Repeat 
process to solve for backwards. QED
-/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin

  assume P Q R,
  apply iff.intro,

  assume A,
  apply and.elim A,
  assume  p qr,
  apply or.elim qr,
  assume q,
  apply or.intro_left,
  apply and.intro,
  exact p ,
  exact q,

  assume r,
  apply or.intro_right,
  apply and.intro,
  exact p,
  exact r,

  assume B,
  apply or.elim B,
  assume pq,
  apply and.elim pq,
  assume p q,
  apply and.intro,
  exact p,
  apply or.intro_left,
  exact q,

  assume pr,
  apply and.elim pr,
  assume p r,
  apply and.intro,
  exact p,
  apply or.intro_right,
  exact r,
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. Next use the elimination rule to show that the forwards is equivalent to
P → Q ∨ R → P ∧ Q ∨ P ∧ R. Use the elimination rule for or  to show that Q → P ∧ Q ∨ P ∧ R.
Next  use the introduction rule for or  to split P ∧ Q ∨ P ∧ R.  Use the introduction
rule for and to prove P∧Q. Use last two steps to prove P∧R.

To solve backwards, use elimination rules for and and or to reach P → Q → P ∧ (Q ∨ R).
Next use the intro rule for and to split into proofs of P and of Q∨R.Use or intro rule
to solve Q∨R. Repeat steps except the first backwards step to solve. QED
-/


example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin

assume P Q R,
apply iff.intro,
--forward
  assume pqr,
  
  apply or.elim pqr,
  assume p,
  apply and.intro,
  apply or.intro_left,
  exact p,
  apply or.intro_left,
  exact p,

  assume qr,
  apply and.intro,
  apply or.intro_right,
  apply and.elim_left qr,

  apply or.intro_right,
  apply and.elim_right qr,

--backward
  assume pqpr,
  have pq : (P ∨ Q):= and.elim_left pqpr,
  have pr : (P ∨ R):= and.elim_right pqpr,
  apply or.elim pr,
  assume p,
  apply or.intro_left,
  exact p,

  assume r,
  apply or.elim pq,
  assume p,
  apply or.intro_left,
  exact p,
  
  assume q,
  apply or.intro_right,
  apply and.intro,
  exact q,
  exact r,
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. For the forward case, use the or elim rule on P ∨ Q ∧ R to establish that
its elements imply (P ∨ Q) ∧ (P ∨ R). Use the intro rule for and followed by the intro rule
for or twice to prove P → (P ∨ Q) ∧ (P ∨ R). Use the and intro rule, followed by the or
intro rule, and elim rule, or intro rulem and finally and elim rule again to prove Q ∧ R → (P ∨ Q) ∧ (P ∨ R).

To solve backwards, have proofs of pq and pr. Next, use the or elim rule followed by the 
or intro rule to solve P → P ∨ Q ∧ R. Next, use the or elim followed by or intro to solve
R → P ∨ Q ∧ R. Finally, use or intro and and intro to solve Q → P ∨ Q ∧ R
-/

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  assume p,
  apply and.elim_left p,

  assume p,
  apply  and.intro,
  exact p,

  apply or.intro_left,
  exact p,
  
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. For forwads use elim rule for and. For backwards, use intro rule
for and followed by intro rule for  or QED
-/

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  assume A,
  apply or.elim A,
  assume p,
  exact p,
  assume pq,
  apply and.elim_left pq,

  assume p,
  apply or.intro_left,
  exact p,
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. For forwards, solve with or elimination followed by and elimination.
For  backwards use or intro rule to solve QED
-/

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  assume A,
  exact true.intro,
  assume T,
  apply or.intro_right,
  exact true.intro,
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. Use the true intro rule to solve forward. Use the or intro rule and true intro
rule to solve backwards QED
-/

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume A,
  apply or.elim A,
  assume p,
  exact p,
  exact false.elim,

  assume p,
  apply or.intro_left,
  exact p,
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. Use or elimination followed by false eliminatino to solve forward.
Use or intro rule to solve backward QED
-/

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume A,
  apply and.elim_left A,

  assume p,
  apply and.intro,
  exact p,

  exact true.intro,
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. Use the and elimination rule to solve forward. For backward, use the 
and intro ruled followed by true intro rule to solve QED
-/

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  assume A,
  apply and.elim_right A,
  exact false.elim,
end
/-
Start by implying the introduction rule for if and only if to split it into two 
propositions. Then we can use the eliination rule for false to solve. QED
-/


