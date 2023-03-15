
def add : nat → nat → nat
| a  zero     := a
| a  (succ b) := succ (add a b)


example : ∀ (n : ℕ), nat.add n 0 = n :=
begin
assume n,
simp [nat.add],
end

/-
An English version of this 
proof might go like this: *We're to prove 
that for any n, n + 0 = n.* Proof: Assume n
is an arbitrary but specific natural number. 
By the first rule/axiom defining nat.add we 
can rewrite n + 0 as n. That's it. As n is
general, the conjecture, n + 0 = n, is true 
for all n. 


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
