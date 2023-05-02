import .A_04_torsors
import algebra.module

def x := 4
#check x



/-
/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
@[protect_proj, ancestor add_monoid add_comm_semigroup]
class add_comm_monoid (M : Type u) extends add_monoid M, add_comm_semigroup M
-/

#check @add_comm_monoid.mk
/-
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

instance : add_comm_monoid rot := 
⟨ 
  rot_add,
  rot_add_assoc,
  r0,
  rot_left_ident,
  rot_right_ident,
  rot_npow,            -- fix multiplicative name
  rot_npow_zero,
  rot_npow_succ,
  rot_add_comm,
⟩ 

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

instance : has_smul ℤ rot := ⟨ rot_zpow ⟩ 

lemma rot_mul_smul : ∀ (x y : ℤ) (b : rot), (x * y) • b = x • y • b := sorry

instance : mul_action ℤ rot :=
⟨
  begin
  assume b,
  cases b,
  repeat {exact rfl},
  end,

  begin
  assume x y b,
  apply rot_mul_smul,       -- sorried
  end,
⟩

lemma rot_smul_zero : ∀ (a : ℤ), a • (0 : rot) = 0 := 
begin
simp [rot_zpow],
end

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

instance : distrib_mul_action ℤ rot :=
⟨
  rot_smul_zero,
  rot_smul_add,
⟩

/-
  (∀ (r s : R) (x : M), (r + s) • x = r • x + s • x) → 
  (∀ (x : M), 0 • x = 0)
-/

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

