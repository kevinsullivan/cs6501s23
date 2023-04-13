
import .A_01_monoids
import group_theory.group_action


inductive tri 
| t0
| t120
| t240


/-
@[ext, class]
structure has_smul (M : Type u_1) (α : Type u_2) :
Type (max u_1 u_2)

    smul : M → α → α
-/



universes u_10 u_11

@[ext, class]
structure mul_action (α : Type u_10) (α : Type u_11) [monoid α] :
Type (max u_10 u_11) :=
(    to_has_smul : has_smul α α)
(    one_smul : ∀ (b : α), 1 • b = b)
(    mul_smul : ∀ (x y : α) (b : α), (x * y) • b = x • y • b)




