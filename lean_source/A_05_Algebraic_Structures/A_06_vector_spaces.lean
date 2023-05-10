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
Torsor over vector space
------------------------

TEXT. -/
#check @add_torsor.mk
/- TEXT:
ℚ is defined in mathlab as having the structure of a vector
space. We can declare it to represent a torsor of points on
one hand, and a vector space of actions, that act on points
additively, on the other. Another name for a torsor over a
vector space is an *affine* space. 

A vector space is a linear space. It has an origin at zero,
some vectors, and more vectors derived by the operations of
inverse and scalar multiplication, by values from a scalar 
*field*. A vector space is linear. Among the rules that 
make it so are that, for any scalars, α and β, and for any
vectors, x and y, the following distributive laws hold: 

- α • (x + y) = α • x + α • y 
- (α + β) • x = α • x + β • x

The upshot is that you can add and scalar multiply vectors
in exactly the ways you'd expect from undergraduate linear
algebra. 

An *affine* space, on the other hand, is a set of points 
all of whose *differences* are all of the vectors. Such
a torsor (of points) has no distinguished origin. Rather,
you can pick any point arbitrarily to serve as an origin,
and now every other point is addressed by a vector added
to that origin point. 

Example: add_torsor ℚ ℚ 

In the following example, which begins the transition to
the next chapter, we formalize a torsor of points over a
vector space, where the points are rational numbers (ℚ),
so are vectors, and so are the scalars. One can readily
verify that all the axioms are satisfied. 

Note: we're using one *copy* of the rationals to stand in 
relation to points (no distinguished origin), another to
stand in relation to vectors, and yet a third to stand in
relation to the scalars by which vectors can be multiplied. 

Formlizing ℚ as a torsor over itself as a vector space is
straightforward, requiring only proofs of the two torsor
laws, where the values are all rationals. The proofs are
in turn by straightforward simplification. 
TEXT. -/

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
-- QUOTE.

/- TEXT:
We can now at least signal our abstract intent by using 
operations that reflect our intended interpretations of
their argment as points, vectors, or scalars. We can in
particular use -ᵥ to computes differences of points; +ᵥ
to represent addition of a vector to a point; and • to
represent scalar multiplication of a vector.  
TEXT. -/

-- QUOTE:
def pnt0 := (0:ℚ)
def pnt1 := (1:ℚ)
def vec1 := pnt1 -ᵥ pnt0    -- see: we do have this operation
def vec2 := (1/2:ℚ) • vec1  -- and scalar multiplication, too
def pnt3 := pnt1 + vec2     -- expect 3/2
#eval pnt3
-- QUOTE. 

/- TEXT:
What we've constructed is thus not only linear algebra, in
the vector space, but affine algebra, in the torsor, including
its vector space of translational actions. We thus have a rich
language now for moving points around, as we might want to do
with robots that we wish to occupy certain points. 

Exercise
--------

Replace ℚ with ℚ × ℚ (pairs of rationals) as the 
vectors, leaving ℚ as the scalar field, and then
establish a torsor of 2-D rational points over this 
now 2-D rational vector space. You now have a 2-D 
rational affine space and its corresponding vector
space of translational actions.
TEXT. -/