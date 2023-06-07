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


def pnt0 := (0:ℚ)
def pnt1 := (1:ℚ)
def vec1 := pnt1 -ᵥ pnt0    -- see: we do have this operation
def vec2 := (1/2:ℚ) • vec1  -- and scalar multiplication, too
def pnt3 := pnt1 + vec2     -- expect 3/2
#eval pnt3

