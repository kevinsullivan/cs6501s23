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
def zero_left_ident_add_nat : ∀ (a : ℕ), (nat.add 0 a = a) 
| 0 := p0
| (nat.succ a') := (step a' (zero_left_ident_add_nat a'))


#reduce zero_left_ident_add_nat 0
#reduce zero_left_ident_add_nat 1
#reduce zero_left_ident_add_nat 2
#reduce zero_left_ident_add_nat 3




#check @nat.rec_on


def base_fac := 1

def step_fac : nat → nat → nat 
| n' fac_n' := (n' + 1) * fac_n'

def fac (n : nat) : nat :=
begin
apply nat.rec_on n,
exact base_fac,
exact step_fac,
end

def fac' : ℕ → ℕ 
| 0 := 1
| (nat.succ n') := (nat.succ n') * fac' n'

#eval fac' 5

#eval fac 5


-- We now have that zero is an *additive identity for ℕ*
#check zero_left_ident_add_nat
#check zero_right_ident_add_nat

theorem zero_ident_add_nat : 
  ∀ (a : ℕ), 
    nat.add nat.zero a = a ∧
    nat.add a nat.zero = a :=
begin 
intro a,
split,
apply (zero_left_ident_add_nat a),
apply (zero_right_ident_add_nat a),
end



-- The induction principle for natural numbers.
#check @nat.rec_on

-- Applying nat.rec_on 
def nat_zero_ident (a : nat) : P a := nat.rec_on a p0 step
#check nat_zero_ident 5
#reduce nat_zero_ident 5  -- proof terms often "unreadable"


example : ∀ a, P a :=
begin
unfold P,
assume a,
apply nat.rec_on a,
exact rfl,    -- base case
exact step,   -- we use already proven lemma
end

-- You can also use Lean's *induction tactic*.
example : ∀ a, P a :=
begin
assume a,
unfold P,
induction a with a' ih, -- applies axiom
exact rfl,              -- base case
simp [nat.add],
assumption,
end



#check nat.mul
/-
def mul : nat → nat → nat
| a 0     := 0
| a (b+1) := (mul a b) + a
-/

theorem mul_one_ident_nat : 
    ∀ (a : ℕ), 
    (nat.mul 1 a = a) ∧
    (nat.mul a 1 = a)  :=
begin
assume a,
split,

-- left conjunct: nat.mul 1 a = a
induction a with a' ih,
-- base case
simp [nat.mul], 
-- inductive case
simp [nat.mul],
rw ih,

-- right conjunct: nat.mul a 1 = a
simp [nat.mul],
apply zero_left_ident_add_nat,
end


theorem nat_add_assoc : 
  ∀ (a b c), 
    nat.add a (nat.add b c) =
    nat.add (nat.add a b) c :=
begin
assume a b c,
induction c with c' ih,

-- base lemma
simp [nat.add],

-- induction lemma
simp [nat.add],
assumption,
end

-- Yay, that's really cool!

-- EXERCISE: Prove that nat.mul is associative

/-
In the middle of trying to prove this theorem, we run into the need
for another theorem, not yet proved: one that shows that nat add and
mul follow the distributive law for multiplication on the left over 
a sum. We present here an example of how one can assume a proof of a
lemma using sorry, with the intent of filling it in later. This gives
you a practical approach to top-down proof construction, just like 
you might follow a discipline of top-down program construction.  
-/
theorem nat_mul_assoc : 
  ∀ (a b c : ℕ), nat.mul a (nat.mul b c) = nat.mul (nat.mul a b) c :=
begin
assume a b c,
induction c with c' ih,
-- base case
simp [nat.mul],
-- inductive case
simp [nat.mul],
rw <- ih,
have mul_distrib_add_nat_left : 
  ∀ x y z, 
    nat.mul x (nat.add y z) = 
    nat.add (nat.mul x y) (nat.mul x z) := 
    sorry,
apply mul_distrib_add_nat_left,
end

-- We leave the proof of left distributivity as an exercise (not trivial)
lemma mul_distrib_add_nat_left : 
  ∀ x y z, 
    nat.mul x (nat.add y z) = 
    nat.add (nat.mul x y) (nat.mul x z) := sorry



universe u

-- general structure (not we've removed "nat" from the name)
structure monoid {α : Type} : Type := mk::
  (op : α  → α  → α )
  (id : α )
  (e : ∀ a, op id a = a ∧ op a id = a)
  (assoc: ∀ a b c, op a (op b c) = op (op a b) c)

def nat_add_monoid := monoid.mk nat.add 0 zero_ident_add_nat nat_add_assoc  
def nat_add_monoid' := monoid.mk nat.add 1 zero_ident_add_nat nat_add_assoc -- caught error
def nat_mul_monoid := monoid.mk nat.mul 1 mul_one_ident_nat nat_mul_assoc   -- sorry 

#reduce nat_add_monoid
#reduce nat_mul_monoid

-- Monoid structure instances 
#reduce foldr nat_add_monoid.op nat_add_monoid.id [1,2,3,4,5]
#reduce foldr nat_mul_monoid.op nat_mul_monoid.id [1,2,3,4,5]


-- A version of foldr that takes a monoid object and uses its op and e values
def foldr' {α : Type} : @monoid α → list α → α  
| (monoid.mk op e _ _) l := foldr op e l

-- Safe use of monoid instances folds
#reduce foldr' nat_add_monoid [1,2,3,4,5]
#reduce foldr' nat_mul_monoid [1,2,3,4,5]


def monoid_list_append' {α : Type}: @monoid (list α) :=
  monoid.mk list.append [] sorry sorry 

#eval foldr' monoid_list_append' [[1,2,3],[4,5,6],[7,8,9]]



-- To be proved
theorem nil_identity_append_list {α : Type u}: 
  ∀ (l : list α), 
    list.append list.nil l = l ∧ 
    list.append l list.nil = l := sorry

-- Here again is the definition list.append (++). 
#check @list.append
/-
def append : list α → list α → list α
| []       l := l
| (h :: s) t := h :: (append s t)
-/


def list_nil_right_ident_for {α : Type u} (l : list α) :=
  list.append l [] = l


lemma list_base {α : Type u} : 
  list_nil_right_ident_for ([] : list α) :=
begin
-- unfold list_nil_right_ident_for,
exact rfl,  -- Lean unfolds name automatically here
end

-- Now let's prove a step lemma.
#check @list.rec_on

lemma list_step {α : Type u} : 
  -- given any new head element, hd
  (Π (hd : α) 
  -- and any existing list, l'
     (l' : list α), 
  -- if [] is a right identity for l'
     list_nil_right_ident_for l' → 
  -- then it's a right identity for one-bigger list
     list_nil_right_ident_for (hd :: l')) :=
begin
unfold list_nil_right_ident_for,
assume hd l' ih,
simp [list.append], -- simplify using second rule of append
assumption,         -- the induction hypothesis finishes it off QED
end 

-- Now we build a recursive function to return proof for any l
#check list_base

def nil_right_ident_append_list' {α : Type} : ∀ (l' : list α), list.append l' [] = l'
| (list.nil) := list_base
| (h::t) := list_step h t (nil_right_ident_append_list' t)

-- Seems to work!
#check nil_right_ident_append_list' [1,2]




#check @list.rec_on
/-
nat.rec_on :                    
  Π {motive : ℕ → Sort u_1}   -- property or return value type
    (n : ℕ),                  -- input argument value
    motive 0 →                -- answer for base case
    (Π ('n : ℕ),              -- step function (higher-order!)
      motive n' → 
      motive n'.succ
    ) → 
  motive n                    -- return values, by recursion
-/

#check @list.rec_on
/-
list.rec_on :
  Π {T : Type u_2}                -- for any list element type
    {motive : list T → Sort u_1}  -- property or return type
    (n : list T),                 -- input argument value  
    motive list.nil →             -- proof/value for base case
    (Π (hd : T)                   -- step function: understand it
       (tl : list T), 
       motive tl → 
       motive (hd :: tl)) → 
  motive n                        -- return value, by recursion


QUESTION: What new element is present in the rule for lists
that isn't involved in the rule for natural numbers?



/-
def append : list α → list α → list α
| []       l := l
| (h :: s) t := h :: (append s t)
-/


theorem nil_left_ident_append_list (α : Type) : ∀ (l : list α), list.nil ++ l = l :=
begin
assume l,
simp [list.append],
end


def nil_right_ident_append (α : Type) : 
  ∀ (l : list α), l ++ [] = l :=
begin
assume l,
induction l,
simp [list.append],
simp,
end





inductive le (n : nat): nat → Prop 
-- n is an implicit firt argument to each constructor
| refl : le (n) n     
| step : ∀ m, le (n) m → le (n) m.succ

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
