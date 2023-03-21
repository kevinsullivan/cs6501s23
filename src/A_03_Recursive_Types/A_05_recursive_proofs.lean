import .A_04_higher_order_functions


-- and a proof
example : ∀ (n : ℕ), nat.add n 0 = n :=
begin
assume n,
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


def P (a : ℕ) : Prop := 0 + a = a

#check P      -- nat → Prop   -- property/predicate


theorem p0 : P 0 := 
begin
unfold P,         -- expand definition of P
                  -- Lean applies def'n of add
                  -- and rfl to finish off proof
end



theorem p1 : P 1 := 
begin
-- add proof p0 to local context for clarity
have p0 := p0,
-- unfold definition of P in P 0
unfold P at p0,
-- rewrite goal by def'n of P
show 0 + 1 = 1,
/-
The challenge is now clear. From a proof
that 0 is a left identity for 0 can we build
a proof that 0 is a left identity for one?
The solution relies on two crucial insights.

First: we can use the *second* axiom of *add*
to rewrite the goal from *add 0 (succ 1)* to 
*succ (add 0 0)*. Be *sure* sure you understand
this point. Go back to the definition of *add*,
look at the second rule, and be sure you see 
that it enables exactly this rewriting. 
The new goal to prove is then:: 
-/ 
show (1 + (0 + 0)) = 1,  -- see def'n of add!
/-
Second, we can use our proof, p0 : (P 0), that 
zero is a left identity for 0 on the right, to 
rewrite 0 + 0 as 0. We're then left with the 
goal to show that *1 + 0 = 1*, with zero *on 
the right*, which Lean then proves for us 
automatically by applying the first rule of 
addition. 
-/
rw p0,
end  


theorem p2 : P 2  :=
begin
have p1 := p1,    -- just for clarity
unfold P at p1,
show 1 + (0 + 1) = 2,
rewrite p1,
end 

-- Wow, can we just keep doing this?

theorem p3 : P 3  :=
begin
have p2 := p2,    -- just for clarity
unfold P at p2,
show 1 + (0 + 2) = 3,
rewrite p2,
end 

theorem zero_left_id_four : P 4  :=
begin
have p3 := p3,    -- just for clarity
unfold P at p3,
show 1 + (0 + 3) = 4,
rewrite p3,
end 
/- Now it looks like that from any nat, *a' : nat*, 
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


def pa : ∀ (a : ℕ), (nat.add 0 a = a) 
| 0 := p0
| (nat.succ a') := (step a' (pa a'))

#check pa   


#reduce pa 0
#reduce pa 1
#reduce pa 2
#reduce pa 3



-- 0 is a left and right identity for nat +
theorem zero_ident_nat_add :
  ∀ (a : ℕ), 
    (0 + a = a) ∧
    (a + 0 = a) :=
begin
assume a,
split,
apply pa,  -- inductive case by left_identity theorem
apply rfl, -- base case is easyend
end


theorem zero_ident_nat_add' : ∀ (a : ℕ), (0:nat).add a = a ∧ a.add 0 = a :=
begin
assume a,
split,
apply pa,
apply rfl,
end

-- KEVIN: Why these complexities around notation?



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


#check @nat.rec_on

def nat_zero_ident (a : nat): P a := nat.rec_on a p0 step
#check nat_zero_ident 5
#reduce nat_zero_ident 5



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
