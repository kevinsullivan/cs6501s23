
import .A_01_monoids
import group_theory.group_action


#check @group
/-
class group (G : Type u) extends div_inv_monoid G :=
(mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
-/


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

#check @monoid




#check @has_inv
#check @has_inv.mk 
/-
Π {α : Type u}, (α → α) → has_inv α

The has_inv typeclass requires an implementation
of a unary operation, inv, on α, and provides a⁻¹ 
as a standard mathematical notation. It does not 
constrain the behavior of inv in any way, leaving
that task to downstream typeclasses that inherit
from this one.  
-/



open rot
def rot_inv : rot → rot           -- HOMEWORK
| r0 := r0
| r120 := r240
| r240 := r120

instance : has_inv rot := ⟨ rot_inv ⟩  -- ⟨ ⟩ applies mk

-- example, cool!
#reduce r120^2


example : ∀ (r : rot), (r⁻¹ * r = 1) := 
begin
assume r,
cases r,
repeat {exact rfl, },
end


def rot_div : rot → rot → rot := λ a b, a * b⁻¹ 
instance : has_div rot := ⟨ rot_div ⟩  
example : r240 / r240 = 1 := rfl


#check @div_inv_monoid.mk 
/-
div_inv_monoid.mk :
  Π -- arguments
    {G : Type u_1} 
    (mul : G → G → G)
    (mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
    (one : G)
    (one_mul : ∀ (a : G), 1 * a = a) 
    (mul_one : ∀ (a : G), a * 1 = a) 
    (npow : ℕ → G → G)
    (npow_zero' : auto_param (∀ (x : G), npow 0 x = 1) (name.mk_string "try_refl_tac" name.anonymous))
    (npow_succ' : auto_param (∀ (n : ℕ) (x : G), npow n.succ x = x * npow n x) (name.mk_string "try_refl_tac" name.anonymous))
    (inv : G → G) 
    (div : G → G → G),  -- comma
    auto_param (∀ (a b : G), a / b = a * b⁻¹) (name.mk_string "try_refl_tac" name.anonymous) →
    Π (zpow : ℤ → G → G),
      auto_param (∀ (a : G), zpow 0 a = 1) (name.mk_string "try_refl_tac" name.anonymous) →
      auto_param (∀ (n : ℕ) (a : G), zpow (int.of_nat n.succ) a = a * zpow (int.of_nat n) a) (name.mk_string "try_refl_tac" name.anonymous) →
      auto_param (∀ (n : ℕ) (a : G), zpow -[1+ n] a = (zpow ↑(n.succ) a)⁻¹) (name.mk_string "try_refl_tac" name.anonymous) →
  div_inv_monoid G
-/


#check int
/-
inductive int : Type
| of_nat : nat → int
| neg_succ_of_nat : nat → int
-/



-- an example

def isNeg : ℤ → bool 
| (int.of_nat n) := ff
| (int.neg_succ_of_nat n) := tt
#eval isNeg (-5 : int)


-- hint: think about rot_npow from monoid
def rot_zpow : ℤ → rot → rot 
| (int.of_nat n) r := rot_npow n r                    -- HOMEWORK 
| (int.neg_succ_of_nat n) r := (rot_npow (n+1) r)⁻¹   -- HOMEWORK

#reduce rot_zpow (-2:ℤ) r240 -- yay! expect 240




-- just to be explicit, we already have the following two proofs
lemma rot_npow_zero : (∀ (x : rot), rot_npow 0 x = 1) :=
   monoid.npow_zero'

lemma rot_npow_succ : (∀ (n : ℕ) (x : rot), rot_npow n.succ x = x * rot_npow n x) :=
  monoid.npow_succ'

-- We need related proofs linking div and inv and proofs of axioms for zpow
lemma rot_div_inv : (∀ (a b : rot), a / b = a * b⁻¹) :=
begin
assume a b,
exact rfl,
end

lemma rot_zpow_non_neg : (∀ (n : ℕ) (a : rot), rot_zpow (int.of_nat n.succ) a = a * rot_zpow (int.of_nat n) a) :=
begin
assume n a,
exact rfl,
end

def rot_zpow_neg : (∀ (n : ℕ) (a : rot), rot_zpow -[1+ n] a = (rot_zpow ↑(n.succ) a)⁻¹) :=
begin
assume n a,
exact rfl,
end

#check @div_inv_monoid.mk
/-
div_inv_monoid.mk :
  Π -- arguments
    {G : Type u_1} 
    (mul : G → G → G)
    (mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
    (one : G)
    (one_mul : ∀ (a : G), 1 * a = a) 
    (mul_one : ∀ (a : G), a * 1 = a) 
    (npow : ℕ → G → G)
    (npow_zero' : auto_param (∀ (x : G), npow 0 x = 1) (name.mk_string "try_refl_tac" name.anonymous))
    (npow_succ' : auto_param (∀ (n : ℕ) (x : G), npow n.succ x = x * npow n x) (name.mk_string "try_refl_tac" name.anonymous))
    (inv : G → G) 
    (div : G → G → G),  -- comma
    auto_param (∀ (a b : G), a / b = a * b⁻¹) (name.mk_string "try_refl_tac" name.anonymous) →
    Π (zpow : ℤ → G → G),
      auto_param (∀ (a : G), zpow 0 a = 1) (name.mk_string "try_refl_tac" name.anonymous) →
      auto_param (∀ (n : ℕ) (a : G), zpow (int.of_nat n.succ) a = a * zpow (int.of_nat n) a) (name.mk_string "try_refl_tac" name.anonymous) →
      auto_param (∀ (n : ℕ) (a : G), zpow -[1+ n] a = (zpow ↑(n.succ) a)⁻¹) (name.mk_string "try_refl_tac" name.anonymous) →
  div_inv_monoid G
-/

#check rot_npow

instance div_inv_monoid_rot : div_inv_monoid rot :=  
⟨
  rot_mul,
  rot_mul_assoc,
  1,
  rot_left_ident,
  rot_right_ident,
  rot_npow,
  rot_npow_zero,                -- autoparam
  rot_npow_succ,                -- autoparam
  rot_inv,
  rot_div,
  rot_div_inv,
  rot_zpow
⟩ 

/-
Now we can see the structure we've built!
The proofs are erased in this presentation
and only the computational data are named.
-/
#reduce @div_inv_monoid_rot 



#check group 
/-
class group (G : Type u) extends div_inv_monoid G :=
(mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
-/
#check @group.mk
/-
Π {G : Type u_1} 
  (mul : G → G → G) 
  (mul_assoc : ∀ (a b c : G), 
  a * b * c = a * (b * c)) 
  (one : G)
  (one_mul : ∀ (a : G), 1 * a = a) 
  (mul_one : ∀ (a : G), a * 1 = a) 
  (npow : ℕ → G → G)
  (npow_zero' : auto_param (∀ (x : G), npow 0 x = 1) 
  (name.mk_string "try_refl_tac" name.anonymous))
  (npow_succ' :
    auto_param (∀ (n : ℕ) (x : G), npow n.succ x = x * npow n x) (name.mk_string "try_refl_tac" name.anonymous))
  (inv : G → G) (div : G → G → G)
  (div_eq_mul_inv : auto_param (∀ (a b : G), a / b = a * b⁻¹) (name.mk_string "try_refl_tac" name.anonymous))
  (zpow : ℤ → G → G)
  (zpow_zero' : auto_param (∀ (a : G), zpow 0 a = 1) (name.mk_string "try_refl_tac" name.anonymous))
  (zpow_succ' :
    auto_param (∀ (n : ℕ) (a : G), zpow (int.of_nat n.succ) a = a * zpow (int.of_nat n) a)
      (name.mk_string "try_refl_tac" name.anonymous))
  (zpow_neg' :
    auto_param (∀ (n : ℕ) (a : G), zpow -[1+ n] a = (zpow ↑(n.succ) a)⁻¹)
      (name.mk_string "try_refl_tac" name.anonymous)), (∀ (a : G), a⁻¹ * a = 1) → 
  group G
-/

lemma rot_left_inv:  (∀ (a : rot), a⁻¹ * a = 1) :=
begin
assume a,
cases a,
repeat {exact rfl},
end


instance : group rot := 
⟨
  rot_mul,
  rot_mul_assoc,
  1,
  rot_left_ident,
  rot_right_ident,
  rot_npow,
  rot_npow_zero,                -- autoparam
  rot_npow_succ,                -- autoparam
  rot_inv,
  rot_div,
  rot_div_inv,
  rot_zpow,
  rot_npow_zero,                -- same proof again
  rot_zpow_non_neg,             -- explicit typing needed
  rot_zpow_neg,                 -- same
  rot_left_inv
⟩ 




#reduce r120 * r120               -- multiplication
#reduce r120⁻¹                    -- inverses
#reduce r120 / r240               -- division
#reduce r120^4                    -- exponentiation by nat
#reduce r120^(4:int)              -- exponentiation by non-negative int
#reduce r120^(-4:int)             -- exponentiation by negative int


