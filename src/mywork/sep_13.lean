namespace implies

axioms ( P Q : Prop)

def if_P_is_true_then_so_is_Q : Prop := P → Q

axiom p :  P
-- assume P is true
-- assume we havea proof  of P (p)

axiom pq :  P → Q
--assume that we havea proof,  pq, of P →  Q 
 
-- intro for implies: assime premise, show conclusion
-- elimnation  rule  for implies: 

#check pq 
#check p
#check (pq p)

/-
suppose P and Q are propositions and  you
know that P → Q and that P are both ty the elimination rule for  → with

Proof:apply the truth of  P → Q to the 
truth of  Pto  derive the  truth  of Q

proof: by the elimination rule for → with pq applied to p
-/
end implies
/-
For All
-/
namespace all

axioms 
 (T: Type) 
 (P :  T  → Prop)
 (t  :  T)

 ( a : ∀ (x : T), P x )

-- does t have property P?

example : P t := a t 
#check a t 





end all