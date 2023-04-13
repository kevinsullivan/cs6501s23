
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
| r0 t0 := t0
| r0 t120 := t120
| r0 t240 := t240
| r120 t0 := t120
| r120 t120 := t240
| r120 t240 := t0
| r240 t0 := t240
| r240 t120 := t0
| r240 t240 := t120

instance : has_smul rot tri := ⟨ mul_rot_tri ⟩ 

#reduce r0 • t0
#reduce r240 • t0
#reduce r240 • t120



lemma foo : ∀ (b : tri), (1 : rot) • b = b :=
begin
assume b,
cases b,
repeat {exact rfl},
end

def bar : ∀ (x y : rot) (b : tri), (x * y) • b = x • y • b :=
begin
assume x y b,
cases b,
repeat {
  cases x,
  repeat {
    cases y,
    repeat {exact rfl},
  }
},
end


instance : mul_action rot tri :=
⟨ 
  foo,
  bar
⟩ 

/-TEXT: 
Discussion
----------



