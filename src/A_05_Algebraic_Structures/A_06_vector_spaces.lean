import .A_05_modules
import data.real.basic 



def K : Type := ℚ     -- scalars
def P : Type := ℚ     -- actions

#check module.mk
/-
Π {R : Type u} {M : Type v} 
  [_inst_1 : semiring R] 
  [_inst_2 : add_comm_monoid M] 
  [_to_distrib_mul_action : distrib_mul_action R M], 
  (∀ (r s : R) (x : M), (r + s) • x = r • x + s • x) → 
  (∀ (x : M), 0 • x = 0) → 
module R M
-/

-- With a scalar field we have a vector space
-- The point are rationals and so are the actions
-- Action/vectors act on point by translation  
instance : module ℚ ℚ :=
⟨
  -- ∀ (r s x : ℚ), (r + s) • x = r • x + s • x
  begin
  assume r s x,
  simp [rat.mul],
  ring,
  end,

  -- ∀ (x : ℚ), 0 • x = 0
  begin
  assume x, 
  simp [rat.mul],
  end
⟩

/-
We have a field. Here, (3:ℚ) is an action,
(1/2:ℚ) is a scalar, and the result of the
scalar multiplication of 1/2 and 3, (3/2:ℚ),
is another action. 
-/

--    scalar  mul vector
#eval (1/2:ℚ)  •  (3:ℚ) 


#check @add_torsor.mk
/-
-/
instance : add_torsor ℚ ℚ := 
⟨
  -- ∀ (p1 p2 : ℚ), p1 -ᵥ p2 +ᵥ p2 = p1
  begin
  assume p1 p2,
  simp,
  end,

  -- ∀ (g p : ℚ), g +ᵥ p -ᵥ p = g
  begin
  assume g p,
  simp,
  end,
⟩ 

/- 
And with that we have geometry again. Points 
are given by rational numbers. Differences 
between points are vectors, and are also given
by rational numbers. Vectors act additively on 
points by translating them. 

Here's an example where we compute a vector as
a difference between two points, which we then
apply to another point. 
-/

--   (vector from torsor)   point
#eval ((3:ℚ) -ᵥ (1/2:ℚ)) +ᵥ (2:ℚ) -- expect (9/2:ℚ)

