
import .A_01_monoids


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



#check @has_inv.mk 
/-
Π {α : Type u}, (α → α) → has_inv α
-/

open rot_syms
def rot_inv : rot_syms → rot_syms           -- HOMEWORK
| r0 := r0
| r120 := r240
| r240 := r120

instance : has_inv rot_syms := ⟨ rot_inv ⟩  -- ⟨ ⟩ applies mk



def rot_div : rot_syms → rot_syms → rot_syms
| a b := a * b⁻¹ 

instance : has_div rot_syms := ⟨ rot_div ⟩  -- HOMEWORK


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



-- hint: think about rot_npow from monoid
def rot_zpow : ℤ → rot_syms → rot_syms 
| (int.of_nat n) r := rot_npow n r                    -- HOMEWORK 
| (int.neg_succ_of_nat n) r := (rot_npow (n+1) r)⁻¹   -- HOMEWORK


-- HOMEWORK

lemma rot_npow_zero : (∀ (x : rot_syms), rot_npow 0 x = 1) :=
begin
assume x,
exact rfl,
end

lemma rot_npow_succ : (∀ (n : ℕ) (x : rot_syms), rot_npow n.succ x = x * rot_npow n x) :=
begin
assume x r,
exact rfl,
end

lemma rot_div_inv : (∀ (a b : rot_syms), a / b = a * b⁻¹) :=
begin
assume a b,
exact rfl,
end

lemma rot_zpow_non_neg : (∀ (n : ℕ) (a : rot_syms), rot_zpow (int.of_nat n.succ) a = a * rot_zpow (int.of_nat n) a) :=
begin
assume n a,
exact rfl,
end

def rot_zpow_neg : (∀ (n : ℕ) (a : rot_syms), rot_zpow -[1+ n] a = (rot_zpow ↑(n.succ) a)⁻¹) :=
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

instance div_inv_monoid_rot_syms : div_inv_monoid rot_syms :=  
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
  rot_npow_zero,
  rot_zpow_non_neg,
  rot_zpow_neg,
⟩ 

#eval @div_inv_monoid_rot_syms 

#check @group
#check @group.mk


-- Examples

#reduce r120 * r120               -- multiplication
#reduce r120⁻¹                    -- inverses
#reduce r120 / r240               -- division
#reduce rot_npow 4 r120           -- exponentiation by non-negative int
#reduce rot_zpow (-4 : int) r120  -- exponentiation by negative int

