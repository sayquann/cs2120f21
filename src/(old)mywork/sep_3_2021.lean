/-
Theorem: Equality is symmetric. In other words 
∀ (T : Type) (x y : T), x = y → y = x

Proof:
First we'll assume that  T is any type and we have objects x and y of this type. 
What remains to shown is that x = y → y = x.
To prove this, we'll assume the premise, that x = y, and in this context we to prove y=x.
But by the axiom of subsititubility of equals, and using the fact x=y, we can rewrite x in the goal as y, yielding y=y as our new proof goal,
but this is true by  the axiom of reflexivity of equality. QED





-/
theorem eq_symm: 
  ∀ (T : Type) (x y : T), x = y → y = x  := 
  begin 
    assume (T : Type), 
    assume (x y : T),
    assume (e : x = y ),
    rw e,
  end 

/-
-/

theorem eq_trans:
  ∀ (T : Type) (x y z : T), x = y →  y=z → x=z :=
  begin
    assume T,
    assume x y z,
    assume e1,
    assume e2,
    rw e1,
    exact e2, 
  end

/- 
x =y and y=z 
proof z =x -/

