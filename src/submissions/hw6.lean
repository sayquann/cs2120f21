import data.set

axioms
  {a: Type}
  (L X Y Z: set a)
  (x: a)

--^this is to be used for all the exercises

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/


-- (x ∈ (L ∩ L)) → (x ∈ L) :=
def problem1:  L ∩ L = L:=
begin
  apply set.ext _,
  assume x,
  split,
  --forwards
  assume y,
  cases y with l r,
  apply l,
  --backwards
  assume z,
  apply and.intro,
  apply z,
  apply z,
end

/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/
def problem2: (X ∪ Y) = (Y ∪ X):=
begin
  apply set.ext _,
  assume x,
  split,
  --forward
  assume y,
  cases y,
  apply or.intro_right,
  exact y,
  apply or.intro_left,
  exact y,
  --backward
  assume y,
  cases y,
  apply or.intro_right,
  exact y,
  apply or.intro_left,
  exact y,
end
/-
Union operator on sets is commutative. Start by assuming x in the sets X and Y. Next, we split the relation into forwards and backwards. Next assume that y is a proof that x ∈ X∪Y. next do case analysis on that proof follwed by the intro rules for or to solve forwards. For backwards do the saame case analysis and intro or rules on a new y that is a proof of x∈Y∪Z.
-/

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/
#check @eq.refl
def problem3_1: X ⊆ X:=
begin
  assume p,
  assume q,
  exact q,
end 

/-
Everything equals itself by the reflexive property of equality.
-/

def problem3_2: ∀ (x∈X) (x∈Y)(x∈Z), x∈X → x∈Z:=
begin
  assume q,
  assume p,
  assume c i o n m,
  apply n,
end

/-
If x∈X, x∈Y, x∈Z, it implies x∈Z form x∈X.
-/


/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

def problem4_1: (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z):=
begin
  apply set.ext,
  assume x,
  split,
  --forward
  assume y,
  cases y with l r,
  cases l,
  apply or.intro_left,
  exact l,
  apply or.intro_right,
  apply or.intro_left,
  exact l,
  apply or.intro_right,
  apply or.intro_right,
  exact r,
  --backward
  assume y,
  cases y with l r,
  apply or.intro_left,
  apply or.intro_left,
  exact l,
  cases r,
  apply or.intro_left,
  apply or.intro_right,
  exact r,
  apply or.intro_right,
  exact r,
end

/-
Union is associative: Assume x is of type a and thus x ∈ X ∪ Y∪ Z ↔ x ∈ X ∪ (Y ∪ Z). Then split this new relation into forward and backward.Assume that y is a proof of x ∈ X ∪ Y ∪ Z Then apply case analysis on y and use the intro rules for or to solve the proof forwards. To solve backwards, do same analysis and application but this time with y being a proof of x ∈ X ∪ (Y ∪ Z).
-/

def problem4_2:(X ∩ Y) ∩ Z = X ∩ (Y ∩ Z):=
begin
  apply set.ext,
  assume x,
  split,
  --forward
  assume q,
  cases q with l r,
  apply and.intro,
  have l2:= and.elim_left l,
  apply l2,
  apply and.intro,
  have l3:= and.elim_right l,
  apply l3,
  apply r,
  --backward
  assume q,
  cases q with l r,
  apply and.intro,
  apply and.intro,
  apply l,
  have r2:= and.elim_left r,
  apply r2,
  have r3:= and.elim_right r,
  apply r3,
end

/-
Intersection is associative: Assume x is of type a and thus x ∈ X ∩ Y ∩ Z ↔ x ∈ X ∩ (Y ∩ Z). Split this into forward and backward. assume q is a proof of x ∈ X ∩ Y ∩ Z. then apply case analysis on q and worrk through the proof using the and intro and elimination rules. For backward do the same but with q being a proof of x ∈ X ∩ (Y ∩ Z)
-/

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/

def problem5: X∩(Y∩Z)=(X∩Y)∩(X∩Z):=
begin
  apply set.ext _,
  assume x,
  split,
  --forward
  assume q,
  cases q with l r,
  cases r with r1 r2,
  apply and.intro,
  apply and.intro,
  apply l,
  apply r1,
  apply and.intro,
  apply l,
  apply r2,
  --backward
  assume q,
  cases q with l r,
  cases l with l1 l2,
  cases r with r1 r2,
  apply and.intro,
  apply l1,
  apply and.intro,
  apply l2,
  apply r2,
end

/-
∩ is left-distributive over ∩: Assume x is of type a and thus x ∈ X ∩ (Y ∩ Z) ↔ x ∈ X ∩ Y ∩ (X ∩ Z). Split this into forward and backward. Assume a q, proof of x ∈ X ∩ (Y ∩ Z). Use case analysis and and intro rules to solve forward. Do the same with backward, with q being a proof of  x∈ X ∩ Y ∩ (X ∩ Z). 
-/

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

def problem6: X∪(Y∩Z)=(X∪Y)∩(X∪Z):=
begin
  apply set.ext _,
  assume x,
  split,
  --forward
  assume q,
  cases q with l r,
  apply and.intro,
  apply or.intro_left,
  apply l,
  apply or.intro_left,
  apply l,
  apply and.intro,
  cases r with r1 r2,
  apply or.intro_right,
  apply r1,
  cases r with r1 r2,
  apply or.intro_right,
  apply r2,
  --backward
  assume q,
  cases q with l r,
  cases l with l1 l2,
  cases r with r1 r2,
  apply or.intro_left,
  apply l1,
  apply or.intro_left,
  apply l1,
  cases r with r1 r2,
  apply or.intro_left,
  apply r1,
  apply or.intro_right,
  apply and.intro,
  apply l2,
  apply r2,
  
end

/-
∪ is left-distributive over ∩: Assume x is of type a and thus x ∈ X ∪ Y ∩ Z ↔ x ∈ (X ∪ Y) ∩ (X ∪ Z). Split this into forwad and backward.  For forward assume q is a proof of x ∈ X ∪ Y ∩ Z. Then use cases analyses with intro rules forr and and or to solve the proof forwards. For backwards assume q is a proof of x ∈ (X ∪ Y) ∩ (X ∪ Z) and then use case analysis and intro rules for or and and to solve the proof.
-/