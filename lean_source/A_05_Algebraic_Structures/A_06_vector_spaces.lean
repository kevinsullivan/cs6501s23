import .A_05_modules
import data.real.basic 

/- TEXT: 

*************
Vector Spaces
*************

A module of actions, with addition, subtraction, and
scalar multiplication (with scalars from a ring, such
as ℤ), becomes a vector space when its scalar ring is
in fact a *field(). That roughly mean that there will
be multiplicative inverses of scalars, so fractions;
and so all *fractions of actions* will also have to be
actions. 

A lack of division is exactly what makes ℤ a ring and 
not a field. We get a ℤ-module with scalars from ℤ, and
with scalar multiplication reduced to iterated addition.

On the other hand ℝ\\{0} is a field, with the usual 
addition, subtraction, and multiplication, but now also 
multiplicative inverses, thus division, and fractions. 

One can take any fraction of a vector and get a vector, 
but a fraction of a symmetry rotation is not necessarily
a symmetry rotation. Our symmetry rotations thus do form 
a module, but not a vector space. Vector spaces unlike
modules have all *fractions of actions* as well as all
sums, differences, and multiples of actions.  

Example: Vector Space
---------------------

A module with a scalar ring that's actually a field is a
vector space. Lean doesn't actually have a vector space
typeclass. One just defines a module with a scalar *field*. 
Our example here takes the rational numbers as vector-like
objects (think of them as 1-D vectors) and rationals, which
do form a field, as the scalars.  
TEXT. -/

-- QUOTE:

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

-- QUOTE. 

/- TEXT:
Example: Torsor
---------------

TEXT. -/
#check @add_torsor.mk
/-
-/
-- QUOTE:
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
-- QUOTE.

/- TEXT:

Exercise
--------

Replace ℚ with ℚ × ℚ (pairs of rationals) as the 
vectors, leaving ℚ as the scalar field, and then
establish a torsor of 2-D rational points over this 
now 2-D rational vector space. Yay, we now have a
2-D rational affine space: a torsor over a vector
space. 
TEXT. -/