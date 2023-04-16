
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
| r0 t := t
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



lemma rot_one_action : ∀ (b : tri), (1 : rot) • b = b :=
begin
assume b,
cases b,
repeat {exact rfl},
end

def rot_prod_action : ∀ (x y : rot) (t : tri), (x * y) • t = x • y • t :=
begin
 
assume x y t,
cases t,

  cases x,
  cases y,
  repeat {exact rfl},
  cases y,
  repeat {exact rfl},
  cases y,
  repeat {exact rfl},

  cases x,
  cases y,
  repeat {exact rfl},
  cases y,
  repeat {exact rfl},
  cases y,
  repeat {exact rfl},
  cases y,
  repeat {exact rfl},

cases x,
repeat { exact rfl,},
cases x,
repeat { exact rfl,},
cases x,
repeat {exact rfl,},

end


instance : mul_action rot tri :=
⟨ 
  rot_one_action,
  rot_prod_action,
⟩ 



/-TEXT: 
Discussion
----------





