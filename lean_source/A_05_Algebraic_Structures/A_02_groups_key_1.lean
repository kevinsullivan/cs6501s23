
import .A_01_monoids

/- TEXT: 

******
Groups
******

In this chapter, we'll turn to a first study of groups. 
We start by showing that there is a way to define a total 
*inverse* function on our monoid elements, and that that 
is enough to impose a *group* structure on them. Then we
will study the concept of *group actions*, wherein we see
group elements as *acting* on objects of another (possibly
the same) type. 

Groups
------

Simply put, a group is an algebraic structure that includes 
all of the structure of a monoid with the addition of an
inverse operator. This operator then makes it possible to
define the related notions of division and inverses in a 
group, defining *div a b* (a / b) to be *(mul a (inv b))*.

A set of objects can be given an associated group structure
by instantiation of the group typeclass. This typeclass, in
turn, extends (another extension of) the monoid typeclass. 
In this section we'll apply the method employed in the last
section to see how to imbue our set of rotational symmetries
with such a group structure.

Let's start top-down, with Lean's group typeclass, and then
take it from there.

Required instances
~~~~~~~~~~~~~~~~~~

TEXT. -/

-- QUOTE:
#check @group
/-
class group (G : Type u) extends div_inv_monoid G :=
(mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
-/

-- What is a div_inv_monoid?
#check @div_inv_monoid
/-
class div_inv_monoid (G : Type u) extends monoid G, has_inv G, has_div G :=
(div := λ a b, a * b⁻¹)
(div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ . try_refl_tac)
(zpow : ℤ → G → G := zpow_rec)
(zpow_zero' : ∀ (a : G), zpow 0 a = 1 . try_refl_tac)
(zpow_succ' :
  ∀ (n : ℕ) (a : G), zpow (int.of_nat n.succ) a = a * zpow (int.of_nat n) a . try_refl_tac)
(zpow_neg' :
  ∀ (n : ℕ) (a : G), zpow (-[1 + n]) a = (zpow n.succ a)⁻¹ . try_refl_tac)
-/

-- has_inv and has_div
#check @has_inv
/-
class has_inv      (α : Type u) := (inv : α → α)
-/
#check @has_div
/-
class has_div      (α : Type u) := (div : α → α)
-/
-- QUOTE.

/- TEXT:

has_inv and has_div
~~~~~~~~~~~~~~~~~~~

An instance of the has_inv typeclass will have one field
value, a total function from group elements to other group 
elements. In the context of a group, it will be cosntrained
to behave as a genuine inverse operation must: that given 
an element, r, it will return an element r⁻¹, such that
r⁻¹ * r = 1 (the group identity element). 

Of course the * operator will have to have an inverse for
every element of the group. We'll now define an inverse
operation for our rotations and will soon show that it 
satisfies the axioms for being a (left) inverse. 
TEXT. -/

-- QUOTE:
open rot

-- Here's our inverse operation
def rot_inv : rot → rot
| 1     :=  1
| r120  :=  r240
| r240  :=  r120

-- Let's put it in a typeclass
instance : has_inv rot := ⟨ rot_inv ⟩

/-
Now here's a division operation
Not use of *notation* from has_mul rot_inv
-/
def rot_div (x y : rot) :=  x * y⁻¹

-- And let's stick it in an instance
instance has_div_rot : has_div rot := ⟨ rot_div ⟩ 

/-
A quick "smoke test." If we divide r240
by r240, we've defined that as the same
as "multiplying" r240 by r240⁻¹, which 
in turn is multiplying r240 by r120, and
that is r0, denoted now by 1. So, hey, if
you divide r240 by itself, you get 1. It
sort of makes sense! 

Exercise: is the same true for r0 and r120?
-/
example :r240 / r240 = 1 := rfl
-- QUOTE.

/- TEXT:

div_inv_monoid
~~~~~~~~~~~~~~

TEXT. -/

-- QUOTE:
#check @div_inv_monoid.mk
/-
Π {G : Type u_1} 
  (mul : G → G → G) 
  (mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
  (one : G)
  (one_mul : ∀ (a : G), 1 * a = a) 
  (mul_one : ∀ (a : G), a * 1 = a) 
  (npow : ℕ → G → G)
  (npow_zero' : auto_param (∀ (x : G), npow 0 x = 1) (name.mk_string "try_refl_tac" name.anonymous))
  (npow_succ' :
    auto_param (∀ (n : ℕ) (x : G), npow n.succ x = x * npow n x) (name.mk_string "try_refl_tac" name.anonymous))
  (inv : G → G) (div : G → G → G),
    auto_param (∀ (a b : G), a / b = a * b⁻¹) (name.mk_string "try_refl_tac" name.anonymous) →
  Π (zpow : ℤ → G → G),
    auto_param (∀ (a : G), zpow 0 a = 1) (name.mk_string "try_refl_tac" name.anonymous) →
    auto_param (∀ (n : ℕ) (a : G), zpow (int.of_nat n.succ) a = a * zpow (int.of_nat n) a)
      (name.mk_string "try_refl_tac" name.anonymous) →
    auto_param (∀ (n : ℕ) (a : G), zpow -[1+ n] a = (zpow ↑(n.succ) a)⁻¹)
      (name.mk_string "try_refl_tac" name.anonymous) →
div_inv_monoid G
-/

-- a little pain; use "show" to force rewrite of (a * b⁻¹)
theorem rot_inv_div : ∀ (a b : rot), a / b = a * b⁻¹ :=
begin
assume a b,
show a/b = a/b,
exact rfl,
end

/-
inductive int : Type
| of_nat : nat → int
| neg_succ_of_nat : nat → int
-/

#check ℤ 

#reduce int.of_nat 3
#reduce int.neg_succ_of_nat 0

def rot_zpow : ℤ → rot → rot 
| (int.of_nat 0) _ := 1
| (int.of_nat (nat.succ n')) r := r * (rot_zpow n' r) 
| (int.neg_succ_of_nat n') r := 1 / (rot_zpow ((int.of_nat n') + 1)) r


/-
SEE Design note on div_inv_monoid/sub_neg_monoid and 
division_monoid/subtraction_monoid in the Lean source
file: 
-/ 

lemma foo : (∀ (a : rot), rot_zpow 0 a = 1) :=
  begin
    assume a,
    cases a,
    show rot_zpow 0 r0 = r0,
    exact rfl,    -- a = r0
    exact rfl,    -- a = r120
    exact rfl,    -- a = r240
end

#reduce rot_zpow 2 r120

instance : div_inv_monoid rot :=  
⟨
  rot_mul,
  rot_mul_assoc,
  1,
  rot_left_ident,
  rot_right_ident,
  rot_npow,
  sorry, -- auto_param (∀ (x : rot), rot_npow 0 x = 1) (name.mk_string "try_refl_tac" name.anonymous) : Prop
  sorry, 
  rot_inv,
  rot_div,
  _,
⟩ 

#check @group
#check @group.mk
#check @group.rec

-- QUOTE.
