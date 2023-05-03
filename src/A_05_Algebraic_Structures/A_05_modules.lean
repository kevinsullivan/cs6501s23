import .A_04_torsors
import algebra.module
import algebra.ring


df

/-
-- here's the module typeclass
class module (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] extends distrib_mul_action R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : M, (0 : R) • x = 0)

-- and here's its constructor
/-
#check @module.mk
/-
module.mk :
  Π {R : Type u_1} 
    {M : Type u_2} 
    [_inst_1 : semiring R] 
    [_inst_2 : add_comm_monoid M]
    [_to_distrib_mul_action : distrib_mul_action R M],
    (∀ (r s : R) (x : M), (r + s) • x = r • x + s • x) → 
    (∀ (x : M), 0 • x = 0) → 
    module R M
-/


/-
-- Here's the actual semiring typeclass definition and constructor. 

@[protect_proj, ancestor non_unital_semiring non_assoc_semiring monoid_with_zero]
class semiring (α : Type u) extends non_unital_semiring α, non_assoc_semiring α, monoid_with_zero α
-/



/-
Here's the additive commutative monoid typeclass. It defines an additive monoid 
with *commutative* `(+)`.

@[protect_proj, ancestor add_monoid add_comm_semigroup]
class add_comm_monoid (M : Type u) extends add_monoid M, add_comm_semigroup M
-/

#check @add_comm_monoid.mk
/-
Here's the constructor. We actually already have every field
value from our prior work except for the proof of commutativity
of (rot) addition required for the last field of this typeclass. 

add_comm_monoid.mk : 
  Π {M : Type u} 
    (add : M → M → M) 
    (add_assoc : ∀ (a b c : M), a + b + c = a + (b + c)) 
    (zero : M) 
    (zero_add : ∀ (a : M), 0 + a = a) 
    (add_zero : ∀ (a : M), a + 0 = a) 
    (nsmul : ℕ → M → M), 
    auto_param (∀ (x : M), nsmul 0 x = 0) (name.mk_string "try_refl_tac" name.anonymous) → 
    auto_param (∀ (n : ℕ) (x : M), nsmul n.succ x = x + nsmul n x) (name.mk_string "try_refl_tac" name.anonymous) → 
    (∀ (a b : M), a + b = b + a) → 
  add_comm_monoid M
-/



#check @distrib_mul_action
/-
@[ext] class distrib_mul_action (M A : Type*) [monoid M] [add_monoid A]
  extends mul_action M A :=
(smul_zero : ∀ (a : M), a • (0 : A) = 0)
(smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y)
-/

#check @mul_action
/-
class mul_action (α : Type*) (β : Type*) [monoid α] extends has_smul α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)
-/


open rot

def rot_add_comm : ∀ (a b : rot), a + b = b + a :=
begin
    assume a b,
    cases a,
    repeat {
      cases b,
      repeat {exact rfl},
    },
  end

-- now we can have our typeclass instance for rot 
instance : add_comm_monoid rot := 
⟨ 
  -- stuff we already have
  rot_add,
  rot_add_assoc,
  r0,
  rot_left_ident,
  rot_right_ident,
  rot_npow,         -- fix multiplicative-sounding name
  rot_npow_zero,
  rot_npow_succ,
  rot_add_comm,     -- the new proof here
⟩ 


instance : has_smul ℤ rot := ⟨ rot_zpow ⟩ 

lemma rot_mul_smul : 
  ∀ (x y : ℤ) (b : rot), (x * y) • b = x • y • b := 
begin
sorry,
end

instance : mul_action ℤ rot :=
⟨
  -- one_smul
  begin
  assume b,
  cases b,
  repeat {exact rfl},
  end,

  -- mul_smul
  begin
  assume x y b,
  apply rot_mul_smul,       -- sorried
  end,
⟩


-- scaling the 0 rotation by any int leaves it as 0. 
lemma rot_smul_zero : ∀ (a : ℤ), a • (0 : rot) = 0 := 
  begin
  simp [rot_zpow],
  end

-- scalaing a sum of rotations is the sum of the scalaed rotations 
lemma rot_smul_add : ∀ (a : ℤ) (x y : rot), a • (x + y) = a • x + a • y :=
  begin
  assume z x y,
  -- annoying: notation is blocking progress, use show to change notation 
  have fix : r0 = (0:rot) := begin exact rfl, end,
  -- by case analysis on x, y
  cases x,
  repeat {
    cases y,
    repeat {
      rw fix, 
      simp [rot_add],
    },
  },
  -- induction on z
  repeat {
  induction z with n negn,
  simp [rot_npow],
  simp [rot_zpow],
  },
  -- by commutativity of rot +
  apply rot_add_comm,
  apply rot_add_comm,
end

-- That's all we need for (distrib_mul_action ℤ rot)
instance : distrib_mul_action ℤ rot :=
⟨
  rot_smul_zero,
  rot_smul_add,
⟩



def z_ring [ring ℤ] (r1 r2 : Z) := r1 * r2
#reduce z_ring 3 4


-- Here it is. But we've left out a proof! TBD. Big TODO!
instance : module ℤ rot :=
⟨ show ∀ (r s : ℤ) (x : rot), (r + s) • x = r • x + s • x,
  begin
  assume r s m,
  sorry,          -- oops
  end,
  begin
  assume x,
  exact rfl,
  end
⟩ 



open tri
#reduce ((3:ℤ) • r120) • t120
#reduce ((-2:ℤ) • r120) • t120
#reduce (((3:ℤ) - (2:ℤ)) • r120) • t120

#check @add_torsor