import algebra.algebra.basic tactic.ring

namespace hidden

-- defining nat type inductively and making numbers
inductive nat : Type
| zero : nat
| succ  (n' : nat) : nat 

def z := nat.zero

#check z
#reduce z

def o := nat.succ (z)

#check o
#reduce o 

def t := nat.succ (o)
#check t  
#reduce t

def f : nat :=
begin
  exact nat.succ (nat.succ t)
end

#reduce f

--making increment functions
def inc' : nat → nat :=
begin
  assume n,
  exact n.succ,
end

#reduce inc' f

def inc :nat → nat 
| n := nat.succ n 

#reduce inc f
--making decrement functions
def dec : nat → nat 
| (nat.zero) := nat.zero
| (nat.succ n') := n'

#reduce dec t
--making addition function
def add : nat → nat → nat
| (nat.zero) (m) := m
| (nat.succ n') (m) := nat.succ (add n' m)

#reduce add o t
--making multiplicaiton function
def mult  : nat → nat → nat 
| (nat.zero) (m) := nat.zero
| (nat.succ n') (m) := add m (mult n' m) 

#reduce mult f z

-- !!maybe exam question: make exponential function
def exp : nat → nat → nat
| (m) (nat.zero) := nat.succ (nat.zero)
| () () := _ 


-- sum to 
theorem sum_to : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := add (nat.succ n') (sum_to n')

#reduce sum_to t


end hidden

def  P : nat → Prop 