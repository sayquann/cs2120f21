-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  split, --apply iff.intro,
  --forward
  assume notpq,
  cases (classical.em P) with p np,
  cases (classical.em Q) with q nq,
  have pandq := and.intro p q,
  have pfalse := notpq pandq,
  exact false.elim pfalse,

  exact or.intro_right (¬P) nq, 
  exact or.intro_left (¬Q) np,
  --backward
  assume notpnotq,
  assume pandq,
  cases notpnotq with  p np,
  have p:= and.elim_left pandq,
  contradiction,
  have q:= and.elim_right pandq,
  contradiction,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume pq,
  --apply and.intro,
  cases (classical.em P) with p np,
  --cases (classical.em Q) with q nq,
  have porq:= or.inl p ,
  have f:= pq porq,
  exact false.elim f,

  cases (classical.em Q) with q nq,
  have  porq:= or.inr q,
  have  f:= pq porq ,
  contradiction,  

  apply and.intro,
  exact  np,
  exact nq,
 
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,

  --forward
  assume prop,
  cases prop,
  apply or.intro_left,
  exact  prop,

  have q:= and.elim_right prop,
  apply  or.intro_right ,
  exact q,

  --backward
  assume pq,
  apply or.elim pq,
  assume p,
  apply or.intro_left,
  exact p,
  assume q,
  cases em P with p np,
  apply or.intro_left,
  exact  p,
  apply or.intro_right,
  apply and.intro,
  exact np,
  exact q,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  --forward
  assume P Q R,
  apply iff.intro,
  assume prop1,
  have porq:= prop1.left ,
  have porr:= prop1.right,
  -- apply or.intro_right,
  -- apply and.intro,
  apply or.elim porq,
  assume p,
  apply or.intro_left,
  exact p,
  assume q,
  apply or.elim porr,
  assume p,
  apply  or.intro_left,
  exact p,
  assume r,
  apply or.intro_right,
  apply and.intro,
  exact q,
  exact r,

  --backward
  assume prop,
  apply or.elim prop,
  assume p,
  apply and.intro,
  apply or.intro_left,
  exact p,
  apply  or.intro_left,
  exact p,

  assume qandr,
  apply and.elim qandr,
  assume q r,
  apply and.intro,
  apply or.intro_right,
  apply q,
  apply or.intro_right,
  apply r,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro,

  --forward,
  assume prop,
  have porq:= prop.left,
  have rors:= prop.right,
  
  apply or.elim porq,
  assume p,
  apply or.elim  rors,
  assume r,
  apply or.intro_left,
  apply and.intro,
  apply p,
  apply r,

  assume s,
  apply or.intro_right,
  apply or.intro_left,
  apply and.intro,
  apply p,
  apply s,
  
  assume q,
  apply or.elim rors,
  assume r,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_left,
  apply and.intro,
  apply q,
  apply r,
  assume s,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_right,
  apply and.intro,
  exact q,
  exact s,

  --backwards
  assume prop,
  apply or.elim prop,
  assume pandr,
  apply and.intro,
  have p:= and.elim_left pandr,
  apply or.intro_left,
  exact p,
  have r := and.elim_right pandr,
  apply or.intro_left,
  exact r,

  assume prop2,
  apply or.elim prop2,
  assume ps,
  apply  and.intro,
  have p:= ps.left,
  apply or.intro_left,
  exact p,
  have s:= ps.right,
  apply or.intro_right,
  exact s,

  assume prop3,
  apply or.elim prop3,
  assume qr,
  apply and.intro,
  have q:= qr.left,
  apply or.intro_right,
  exact q,
  have r := qr.right,
  apply or.intro_left,
  exact r,

  assume qs,
  apply and.intro,
  have q:=qs.left,
  apply or.intro_right,
  exact q,

  have s:= qs.right,
  apply or.intro_right,
  exact s,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∀ (n : ℕ ), n ≠ 0 ∨ n=0 :=
begin
  assume n,
  apply or.intro_right,
  cases n,
  apply eq.refl,
  -- i dont know where to go 
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro,

  --forward
  assume pq,
  cases (classical.em P) with p np,
  have q:= pq p,
  apply or.intro_right,
  exact q,
  apply or.intro_left,
  exact np,
  --backward
  assume npq,
  assume p,
  apply or.elim(classical.em Q),
  assume q,
  exact  q,
  assume nq,
  apply or.elim npq,
  assume np,
  contradiction,
  assume q,
  apply q,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pq,
  assume nq,
  cases  (classical.em P) with p np,
  have q:=  pq p,
  apply not.intro,
  contradiction,
  exact np,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume  P Q,
  assume  npnq,
  assume q,
  cases (classical.em P) with p np,
  exact p,
  have nq:=  npnq np,
  contradiction,
end

