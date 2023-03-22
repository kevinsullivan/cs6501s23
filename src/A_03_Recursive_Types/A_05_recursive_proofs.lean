import .A_04_higher_order_functions


-- and a proof, zero on the right
example : ∀ (a : ℕ), nat.add a nat.zero = a :=
begin
assume a,
simp [nat.add],
end



example : ∀ n, nat.add nat.zero n = n :=
begin
assume n,
simp [nat.add],
-- that didn't help; we're stuck!
end


example : ∀ n, nat.add nat.zero n = n :=
begin
assume n,
cases n with n',
-- first case: zero's also on the right
simp [nat.add],
-- second case, argument is succ of some n'
-- how to show 0 + (succ n') = (succ n')
-- but again we're stuck
simp [nat.add],
-- basically back where we started; stuck.
end



-- The property we want to prove is universal
def P (a : ℕ) : Prop := nat.add nat.zero a = a

#check P      -- nat → Prop   -- property/predicate


theorem p0 : P 0 := 
begin
unfold P,         -- expand definition of P
simp [nat.add],        -- rfl to finish off proof

end


#check p0

theorem p1 : P 1 := 
begin
unfold P,
have ih := p0,
unfold P at ih,
show nat.succ (nat.add nat.zero nat.zero) = 1, -- first rule of add
rw ih,
end


theorem p2 : P 2  :=
begin
unfold P,
have ih := p1,
show 1 + (0 + 1) = 2, -- second rule of add
unfold P at ih,       -- use ih, Lean automation
end 

-- Wow, can we just keep doing this?

theorem p3 : P 3  :=
begin
unfold P,
have ih := p2,    -- just for clarity
show 1 + (0 + 2) = 3,
unfold P at ih,
end 

theorem p4 : P 4  :=
begin
have ih := p3,    -- just for clarity
show 1 + (0 + 3) = 4,
unfold P at ih,
end 

/- It looks like that from any nat, *a' : nat*, 
and a proof of *P a'* we can prove *P (a' + 1)*.
-/


lemma step : ∀ (a' : ℕ), P a' → P (a'.succ) :=
begin
assume a' ih,
unfold P at ih,
unfold P,
-- some tedious rewriting of notations is needed
-- Lean confirms that these rewrites are valid
show nat.add 0 a'.succ = a'.succ,
-- now this simplification works
simp [nat.add],
-- same problem again
show 0 + a' = a',
/- 
We've thus reduced the original goal to the
goal of proving the hypothesis that we have
already assumed (implication introduction). 
-/
apply ih,
end


-- formerly called pa (in class)
def zero_left_ident_add : ∀ (a : ℕ), (nat.add 0 a = a) 
| 0 := p0
| (nat.succ a') := (step a' (zero_left_ident_add a'))

#check zero_left_ident_add  
-- ∀ (a : ℕ), 0.add a = a!



#reduce zero_left_ident_add 0
#reduce zero_left_ident_add 1
#reduce zero_left_ident_add 2
#reduce zero_left_ident_add 3



-- 0 is a left and right identity for nat +
theorem zero_ident_nat_add :
  ∀ (a : ℕ), 
    (nat.add 0 a = a) ∧
    (nat.add a 0 = a) :=
begin
assume a,
split,
apply zero_left_ident_add,  -- inductive case
simp [nat.add],             -- base case is easyend
end


theorem zero_ident_nat_add' : ∀ (a : ℕ), (0:nat).add a = a ∧ a.add 0 = a :=
begin
assume a,
split,
apply zero_left_ident_add,
apply rfl,
end



-- The induction principle for natural numbers.
#check @nat.rec_on

-- Applying nat.rec_on 
def nat_zero_ident (a : nat) : P a := nat.rec_on a p0 step
#check nat_zero_ident 5
#reduce nat_zero_ident 5  -- proof terms often "unreadable"


example : ∀ a, P a :=
begin
assume a,
apply nat.rec_on a,
exact rfl,    -- base case
exact step,   -- we use already proven lemma
end

-- You can also use Lean's *induction tactic*.
example : ∀ a, P a :=
begin
assume a,
induction a with a' ih, -- applies axiom
exact rfl,              -- base case
unfold P,               -- inductive case
unfold P at ih,
simp [nat.add],
assumption,
end


#check nat.mul
/-
def mul : nat → nat → nat
| a 0     := 0
| a (b+1) := (mul a b) + a
-/

-- 
def mul_one_left_ident_prop := ∀ a, nat.mul 1 a = a
def mul_one_right_ident_prop := ∀ a, nat.mul a 1 = a
def mul_one_ident_prop := mul_one_right_ident_prop ∧ mul_one_left_ident_prop

theorem mul_one_ident : mul_one_ident_prop :=
begin
split,
_         -- Replace this placeholder with your proof
end


universe u

-- general structure
structure nat_monoid : Type := mk::
  (op : nat → nat → nat)
  (id : ℕ)
  (e : ∀ a, op id a = a ∧ op a id = a)
  (assoc: ∀ a b c, op a (op b c) = op (op a b) c)

def nat_add_monoid := nat_monoid.mk   nat.add 0 zero_ident_nat_add' sorry  
def nat_add_monoid' := nat_monoid.mk  nat.add 1 zero_ident_nat_add' sorry  -- yay caught error
def nat_mul_monoid := nat_monoid.mk   nat.mul 1 sorry sorry                -- no checking here 

-- EXERCISES: Construct proofs to fill in the *sorry*s.

-- Monoid structure instances 
#reduce foldr nat_add_monoid.op nat_add_monoid.id [1,2,3,4,5]
#reduce foldr nat_mul_monoid.op nat_mul_monoid.id [1,2,3,4,5]


-- A version of foldr that takes a monoid object and uses its op and e values
def foldr' {α β : Type} : nat_monoid → list nat → nat
| (nat_monoid.mk op e _ _) l := foldr op e l

-- Safe use of monoid instances folds
#reduce foldr' nat_add_monoid [1,2,3,4,5]
#reduce foldr' nat_mul_monoid [1,2,3,4,5]




-- proving right identity is trivial just as for addition
example (α : Type) : ∀ (l : list α), list.nil ++ l = l :=
begin
assume l,
simp [list.append],
end


def nil_left_ident_app (α : Type) : ∀ (l : list α), l ++ list.nil = l :=
begin
assume l,
cases l with h t,
-- base case
simp [list.append],   -- uses first rule
-- recursive case
simp [list.append],   -- why does this work?
end 

-- Here's another formal demonstration of the same point
variables (α : Type) (a : α) (l : list α) 
example: list.nil ++ l = l := by simp    -- first rule
example : l ++ list.nil  = l := by simp  -- by [simp] lemma in Lean library



inductive le (n : nat): nat → Prop 
-- n is an implicit firt argument to each constructor
| refl : le /-n-/ n     
| step : ∀ m, le /-n-/ m → le /-n-/ m.succ

-- you can see it in the types of the constructors
#check @le.refl
#check @le.step


example : le 0 0 :=
begin
apply le.refl,
end 

example : le 3 3 :=
begin
apply le.refl,
end 

example : le 0 1 :=
begin
apply le.step,
apply le.refl,
end 

example : le 0 3 :=
begin
apply le.step,
apply le.step,
apply le.step,
apply le.refl,
end 

-- here's the same example using Lean's version of "le"
-- it's called nat.less_than_or_equal
example : 0 ≤ 3 :=
begin
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
-- apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.refl,
end 

-- repeat tactical goes too far; use iterate instead
example : 1 ≤ 4 :=
begin
-- repeat {apply nat.less_than_or_equal.step},
iterate 3 {apply nat.less_than_or_equal.step},
apply nat.less_than_or_equal.refl,
end 
