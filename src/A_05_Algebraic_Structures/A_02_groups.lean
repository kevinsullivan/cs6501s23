
import .A_01_monoids


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


-- what are has_inv and has_div
#check @has_inv
/-
class has_inv      (α : Type u) := (inv : α → α)

An instance of has_inv holds a single unary operator, inv, 
on group elements of type α, and provides the notation, a⁻¹, 
to mean (inv a). 
-/
#check @has_div
/-
class has_div      (α : Type u) := (div : α → α → α)

An instance of has_div holds a single binary operator, div, 
on group elements of type α, and provides the notation, a/b 
to mean (mul a (inv b)), or (add a (inv b)), depending on
whether one is working with a multiplicative or additive
group. The notion of division is generalized to any group
in this way. 
-/



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


-- Here's our inverse operation
def rot_inv : rot_syms → rot_syms := _
-- it comes with ⁻¹ as a notation

-- Let's stick it in a has_inv instance for rot_syms
instance : has_inv rot_syms := _


-- Here's our rotation-specific division operation
def rot_div (x y : rot_syms) :=  x * y⁻¹
-- note use of notations from monoid (*) and has_inv

-- Now wecan instantiate has_div for rot_syms 
instance has_div_rot_syms : has_div rot_syms := _
-- thus overloading div(ision) (/) for rot_syms


/-
Verify test correctness in your head by 
first expanding the definition of div, then
unfolding the application of ⁻¹, and finally
reasoning about the "geometry" of the example. 
-/
example :r240 / r240 = 1 := rfl



-- inductive definition of e int (with standard notation ℤ)
#check int
/-
inductive int : Type
| of_nat : nat → int
| neg_succ_of_nat : nat → int
-/



-- hint: think about rot_npow from monoid
def zpow_rot_syms : ℤ → rot_syms → rot_syms 
| (int.of_nat n) r := _           -- reminder: something about rot_npow, hmmm ...
| (int.neg_succ_of_nat n) r := _  -- reminder: rot_npow (and a negative exponent)




-- a little pain; use "show" to force rewrite of (a * b⁻¹)
theorem rot_inv_div : ∀ (a b : rot_syms), a / b = a * b⁻¹ :=
begin
end


/-
SEE Design note on div_inv_monoid/sub_neg_monoid and 
division_monoid/subtraction_monoid in the Lean source
file. Now let's build our group typeclass instance for
rot_syms.
-/ 

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

instance div_inv_monoid_rot_syms : div_inv_monoid rot_syms :=  
⟨
  rot_mul,
  rot_mul_assoc,
  1,
  rot_left_ident,
  rot_right_ident,
  rot_npow,
  _,                -- Lean infers these auto_param values
  _,
  rot_inv,
  rot_div,
  _,
  zpow_rot_syms,
  _,
  _,
  _
⟩ 

#eval @div_inv_monoid_rot_syms 

#check @group
#check @group.mk


