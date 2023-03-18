
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
-- oops, that didn't help; we're stuck!
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


-- a proof-returning function defined by cases
-- takes any n and returns a proof of 0 + n = n
def zero_left_ident_n : ∀ n, (nat.add 0 n = n)
| nat.zero := by simp [nat.add] -- base case
| (nat.succ n') :=              -- recursive case
  begin 
  simp [nat.add],               -- applies second rule and ...
                                -- removes succ on each side
                                -- by injectivity of constructors
                                -- inherent in inductive definitions
  exact (zero_left_ident_n n'), -- prove result recursively 
  end 

-- eyeball check of the recursive structure of these proofs!
#reduce zero_left_ident_n 0     -- the proof term is unpretty (just eyeball it)
#reduce zero_left_ident_n 1     -- the proof for 1 buids on the proof for 0
#reduce zero_left_ident_n 2     -- the proof for 2 buids on the proof for 1
                                -- and we see we can build such a proof for any n
                                -- therefore 0 is a left identity for addition




/- 
Here's the definition of list.append.
It asserts that [] is a left identity axiomatically. 

def append : list α → list α → list α
| []       l := l
| (h :: s) t := h :: (append s t)
-/

-- proving right identity is trivial just as for addition
example (α : Type) : ∀ (l : list α), list.nil ++ l = l :=
begin
assume l,
simp [list.append],
end

/-TEXT:
We run into the same problem as we did before if we take a
naive approach to trying to prove that nil is also a left
identity for ++. And the solution is once again to define
a recursive function by case analysis on l that constructs
a proof of *nil ++ l = l* for any list l. If l = list.nil,
the proof of nil ++ nil is given by the first rule of list
append, otherwise l = (h::t), and we need to prove that
nil ++ h::t = h::t. By the second axiom of list append,
we can rewrite nil ++ h::t as h::(nil ++ t), where we can
obtain (and then us) a proof that nil ++ t = t by recursion,
terminating when t =nil. 

Fortunately, Lean's library already contains a proof that
nil is a right identity, and it's annotated as *[simp]*,
which means that the *simp* tactic will try to use it to
prove our goal. In other words, we can use [simp] to prove
the harder case precisely because someone else has already
done the work for us; and they did it recursively just as
we did to show that 0 is a right identity for addition. 

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
