import linear_algebra.affine_space.basic
import .A_04_torsors
import group_theory.group_action


-- See: they're the same. 

#check @add_torsor
/-
add_torsor : 
  Π (G : out_param (Type u_1)), 
    Type u_2 → 
  Π [_inst_1 : out_param (add_group G)], 
    Type (max u_1 u_2)-/

open_locale affine
#check affine_space
/-
affine_space : 
  Π (G : out_param (Type u_1)), 
    Type u_2 → 
  Π [_inst_1 : out_param (add_group G)], 
    Type (max u_1 u_2)
-/

