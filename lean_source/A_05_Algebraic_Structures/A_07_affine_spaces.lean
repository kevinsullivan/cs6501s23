import linear_algebra.affine_space.basic
import .A_04_torsors
import group_theory.group_action

/- TEXT: 

*************
Affine Spaces
*************

`affine_space <https://leanprover-community.github.io/mathlib_docs/linear_algebra/affine_space/basic.html>_`

In this section we'll make sense of the statement that an 
affine space is just a torsor whose action/difference set
is not just a group but a vector space. Differences between
points are vectors in a vector space, and these operate on
points in the torsor, in turn, by *translating* them. 

In Lean, *affine_space V P* is just another notation for 
*add_torsor V P* where the action set, V, has not only a
group structure, but monoid, group, module, vector space.  

TEXT: -/

-- QUOTE:

-- add_torsor and affine space same here in Lean

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

#check add_torsor.mk

-- Formal definition of affine_space is weak:
-- Doesn't require G be a vector space. It's 
-- just another name for additive torsor. Hmm.
instance : affine_space rot tri :=
⟨ 
  begin
  assume p1 p2,
  cases p1,
  repeat { cases p2, repeat {exact rfl}},
  end,
  begin
  assume g p,
  cases g,
  repeat { cases p, repeat {exact rfl}}
  end
⟩ 
-- QUOTE.