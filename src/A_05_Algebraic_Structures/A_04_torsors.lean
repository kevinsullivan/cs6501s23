import .A_03_group_actions
import algebra.add_torsor


/-
structure add_torsor (G : out_param (Type u_1)) (P : Type u_2) [out_param (add_group G)] :
Type (max u_1 u_2)
    to_add_action : add_action G P    -- action of group elements on triangles (+ᵥ)
    to_has_vsub : has_vsub G P        -- binary difference operation on triangles (-ᵥ)
    nonempty : nonempty P             -- a condition to be a torsor is non-emptiness

    -- The torsor axioms; what do they mean geometrically? 
    vsub_vadd' : ∀ (p1 p2 : P), p1 -ᵥ p2 +ᵥ p2 = p1
    vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g
-/




-- renaming
def rot_add := rot_mul
def rot_add_assoc := rot_mul_assoc
def foo := rot_npow

#check @add_monoid.mk

/-
Π {M : Type u_1} 
  (add : M → M → M),
  (∀ (a b c : M), a + b + c = a + (b + c)) →
  Π (zero : M) 
  (zero_add : ∀ (a : M), 0 + a = a) 
  (add_zero : ∀ (a : M), a + 0 = a) 
  (nsmul : ℕ → M → M),
  auto_param (∀ (x : M), nsmul 0 x = 0) (name.mk_string "try_refl_tac" name.anonymous) →
  auto_param (∀ (n : ℕ) (x : M), nsmul n.succ x = x + nsmul n x)
    (name.mk_string "try_refl_tac" name.anonymous) →
  add_monoid MLea
-/


open rot
instance : add_monoid rot :=
⟨
  rot_add,        -- same operation now viewed as addition
  rot_add_assoc,  -- same trick
  r0,
  begin 
    assume a, 
    cases a, 
    repeat {exact rfl}, 
  end,
  begin 
    assume a, 
    cases a, 
    repeat {exact rfl}, 
  end,
  foo,    -- TODO: fix naming
⟩ 

-- The add_monoid structure gives us addition and the + notation for it
-- We think of monoid addition as akin to vector addition
#reduce r120 + r120    -- overloaded +
#reduce r120 + r0      -- overloaded 0 


#check @add_group.mk
/-
add_group.mk :
  Π 
    {A : Type u_1} 
    (add : A → A → A) 
    (add_assoc : ∀ (a b c : A), a + b + c = a + (b + c)) 
    (zero : A)
    (zero_add : ∀ (a : A), 0 + a = a)
    (add_zero : ∀ (a : A), a + 0 = a) 
    (nsmul : ℕ → A → A)
    (nsmul_zero' : auto_param (∀ (x : A), nsmul 0 x = 0) (name.mk_string "try_refl_tac" name.anonymous))
    (nsmul_succ' :
      auto_param (∀ (n : ℕ) (x : A), nsmul n.succ x = x + nsmul n x) (name.mk_string "try_refl_tac" name.anonymous))
    (neg : A → A) 
    (sub : A → A → A)
    (sub_eq_add_neg : auto_param (∀ (a b : A), a - b = a + -b) (name.mk_string "try_refl_tac" name.anonymous))
    (zsmul : ℤ → A → A)
    (zsmul_zero' : auto_param (∀ (a : A), zsmul 0 a = 0) (name.mk_string "try_refl_tac" name.anonymous))
    (zsmul_succ' :
      auto_param (∀ (n : ℕ) (a : A), zsmul (int.of_nat n.succ) a = a + zsmul (int.of_nat n) a)
        (name.mk_string "try_refl_tac" name.anonymous))
    (zsmul_neg' :
      auto_param (∀ (n : ℕ) (a : A), zsmul -[1+ n] a = -zsmul ↑(n.succ) a)
        (name.mk_string "try_refl_tac" name.anonymous)), (∀ (a : A), -a + a = 0) → add_group A
-/

instance : add_group rot :=
⟨
  rot_add,        -- stealing it for use here
  rot_add_assoc,  -- even works for this
  0,              -- r0 denoted 0 is additive identity 
  rot_left_ident,
  rot_right_ident,
  foo,       -- again reusing mult operator
  -- nsmul 0
  begin assume x, exact rfl, end,
  begin 
    assume n x,
    simp [foo],   -- TODO: fix naming
    exact rfl,
  end,
  rot_inv,
  (λ r1 r2, r1 + (rot_inv r2)),
  begin
    assume a b,
    exact rfl,
  end,
  rot_zpow,       -- TODO: fix naming
  begin
    assume r,
    exact rfl,
  end,
  begin
    assume n a,
    exact rfl,
  end,
  begin
    assume n a,
    exact rfl,
  end,
  begin
    assume a,
    cases a,
    repeat {exact rfl,} 
  end,
⟩
-- So here we have the add_group we need for torsor
-- What it gives us (because of inverses) is subtraction

#reduce r120 - r120



-- view mul action, mul_rot_tri, as an additive action
-- a rotation "adds itself" to any tri to rotate it thusly

-- We need additive action, borrow mult version (hack)
def add_rot_tri := mul_rot_tri
instance : has_vadd rot tri := ⟨ add_rot_tri ⟩ 

-- Now we've got the "action"



/-
@[ext, class]
structure add_action (G : Type u_10) (P : Type u_11) [add_monoid G] :
Type (max u_10 u_11)
    to_has_vadd : has_vadd G P
    zero_vadd : ∀ (p : P), 0 +ᵥ p = p
    add_vadd : ∀ (g₁ g₂ : G) (p : P), g₁ + g₂ +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)
-/

#check @add_action.mk
/-
add_action.mk : 
Π 
  {G : Type u_10} 
  {P : Type u_11} 
  [_inst_1 : add_monoid G] 
  [_to_has_vadd : has_vadd G P], 
(∀ (p : P), 0 +ᵥ p = p) → 
(∀ (g₁ g₂ : G) (p : P), g₁ + g₂ +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)) → 
add_action G P
-/

instance : add_action rot tri :=
⟨
  -- (∀ (p : P), 0 +ᵥ p = p)
  begin
    assume t, 
    cases t,
    repeat {exact rfl,}
  end,  

  -- (∀ (g₁ g₂ : G) (p : P), g₁ + g₂ +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p))  
  begin
    assume g h t,
    cases t,
      repeat {
        cases g,
          repeat { 
            cases h, 
              repeat { exact rfl }
          }
      },  
  end  
⟩



-- With this additive action we can now instantiate torsor rot tri. 

#check @add_torsor
/-
class add_torsor (G : out_param Type*) (P : Type*) [out_param $ add_group G]
  extends add_action G P, has_vsub G P :=
[nonempty : nonempty P]
(vsub_vadd' : ∀ (p1 p2 : P), (p1 -ᵥ p2 : G) +ᵥ p2 = p1)
(vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g)
-/

-- we need nonemtpy tri
instance : nonempty tri := ⟨ tri.t0 ⟩   -- maybe open namespace?

-- we need has_vsub rot tri
def vsub_rot_tri : tri → tri → rot  
| tri.t0 tri.t0 := 0
| tri.t0 tri.t120 := r240
| tri.t0 tri.t240 := r120
| tri.t120 tri.t0 := r120
| tri.t120 tri.t120 := 0
| tri.t120 tri.t240 := r240
| tri.t240 tri.t0 := r240
| tri.t240 tri.t120 := r120
| tri.t240 tri.t240 := 0
instance : has_vsub rot tri := ⟨ vsub_rot_tri⟩ 

-- Ready!
#check @add_torsor.mk
/-
add_torsor.mk : 
Π 
  {G : out_param (Type u_1)} 
  {P : Type u_2} 
  [_inst_1 : out_param (add_group G)] 
  [_to_add_action : add_action G P] 
  [_to_has_vsub : has_vsub G P] 
  [nonempty : nonempty P], 
(∀ (p1 p2 : P), p1 -ᵥ p2 +ᵥ p2 = p1) → 
(∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g) → 
add_torsor G P
-/

instance : add_torsor rot tri := add_torsor.mk 

-- ∀ (p1 p2 : ?m_1), p1 -ᵥ p2 +ᵥ p2 = p1 : Prop
begin
  assume p1 p2,
  cases p1,
  repeat {
    cases p2,
    repeat {exact rfl},
  }
end 

-- (∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g)
begin
  assume g p,
  cases g,
  repeat {
    cases p,
    repeat {exact rfl},
  },
end


#reduce r120 +ᵥ r240 +ᵥ -r0 +ᵥ -r120 +ᵥ r0 +ᵥ tri.t0  -- five costly actions (+ᵥ)
-- r120 acting on the result of r240 acting on the result of ... r0 acting on t0


#reduce r120  + r240  -  r0  -  r120  + r0 +ᵥ tri.t0  -- add in group, then just one!
-- the sum of r120 and r240 and ... acting on t0.


