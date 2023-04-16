
import .A_01_monoids
import group_theory.mul_action


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
    auto_param 
        (∀ (x : M), nsmul 0 x = 0) 
        (name.mk_string "try_refl_tac" name.anonymous) → 
    auto_param 
        (∀ (n : ℕ) (x : M), nsmul n.succ x = x + nsmul n x) 
        (name.mk_string "try_refl_tac" name.anonymous) → 
  (∀ (a b : M), a + b = b + a) → 
add_comm_monoid M
-/


#check @semiring 



inductive tri 


/-
@[ext, class]
structure has_smul (M : Type u_1) (α : Type u_2) :
Type (max u_1 u_2)
    smul : M → α → α
-/



/-
universes u_10 u_11

@[ext, class]
structure mul_action (α : Type u_10) (α : Type u_11) [monoid α] :
Type (max u_10 u_11) :=
(    to_has_smul : has_smul α α)
(    one_smul : ∀ (b : α), 1 • b = b)
(    mul_smul : ∀ (x y : α) (b : α), (x * y) • b = x • y • b)
-/



open rot
open tri

def mul_rot_tri : rot → tri → tri
-- fill in


instance : has_smul rot tri := _

instance : mul_action rot tri :=
sorry




