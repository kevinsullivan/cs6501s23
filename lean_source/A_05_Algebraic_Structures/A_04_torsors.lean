import .A_03_group_actions
import algebra.add_torsor

/- TEXT: 

*******
Torsors
*******

Introduction
------------

Might it be that the triangle elements of tri can be 
understood as points in a space, and that elements of rot 
can be understood as differences between points in a way
that turns the points into a torsor over the group of
rotations? 

From a group action we know that the effect of a sequence 
of actions on a triangle is the same as the action of the 
sum (in the group) of the actions.

When actions are expensive (e.g., involving actions on
real, physical things), it can be hugely beneficial to
compute the sum then just take one action that gets to 
the same end result.

In this chapter we'll see how to formalize this idea 
again using our example of the rotational symmetry 
group of an equilateral triangle. We will the see that
the set of triangles themselves, with an appropriate
*difference* operation, constitutes a torsor for that
group. 

When the actions form a group (an additive group), we 
can combine them using addition and subtraction. If the
actions form a richer structure, such as a *module* or a
*vector space*, then we can do even richer mathematics 
with actions before applying them. 

The "architecture" of a structured collection of actions 
acting on a set of objects 

Readings
--------

- `Torsors made easy <https://math.ucr.edu/home/baez/torsors.html>`_
- `Additive torsors in Lean <https://github.com/leanprover-community/mathlib/blob/master/src/algebra/add_torsor.lean>`_
- `Prof. Baez page <https://math.ucr.edu/home/baez/>`_

From Baez, Torsors made easy:

- Newtonian Physics: Energy is relative to an arbitrary zero. Energy differences lie in the group of real numbers R, but energies themselves do not: they lie in an R-torsor. 
- Electromagnetism: Voltage is relative to an arbitrary zero. Voltage differences lie in the group of real numbers R, but voltages themselves do not: they lie in an R-torsor. 
- Quantum Mechanics: Phases are relative. “[W]e can multiply the phase of a quantum state by any unit complex number without changing the physics….What makes sense … is to talk about the relative phase between two states that differ only by a phase.” Relative phases lie in the group of unit complex numbers, which is called U(1), but phases themselves do not: they lie in a U(1)-torsor.

- An affine space *A* is a torsor for a vector space *V*.

Typeclass
---------

We'll  now set out to formalize the notion of a G-torsor as
an instance of the typeclass, add_torsor G P, for G = rot and
P = tri. Here G is the set of rotations as an *additive* group. 

Paraphrasing from the mathlib documentation, an (add_torsor 
G P) gives a structure to a nonempty type P, acted on by an 
add_group G with a (transitive & free) action given by the +ᵥ 
operation on G and corresponding subtraction given by the -ᵥ 
operation. In the case of G being a vector space, P is then 
an affine space.

TEXT. -/
#check rot_zpow
-- QUOTE:
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
-- QUOTE.

/- TIME:

Instances
---------

First we need to recast our multiplicative group, rot, 
as an additive group. And just as (mul) group inherits 
from (mul) monoid, we'll need to have add_group inherit
from add_monoid. This and related steps will be easy as
we can just relabel our existing mul operation as add,
and all the proofs (e.g., of associativity) just carry
through.

add_monoid rot
~~~~~~~~~~~~~~

To structure rot as an additive group, we need first to 
structure it as as additive monoid. So we now take these
steps: first an *additive* monoid of rotations, the the
corresponding additive group.  
TEXT. -/

-- QUOTE:
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
-- QUOTE.

/- TEXT:

Now we can formulate our collection of rotations as an additive group. 

add_group rot
~~~~~~~~~~~~~

TEXT. -/

-- QUOTE: 
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

-- QUOTE.

/- TEXT:

Next we formulate the action of a rotation on a triange. 
We do it in two steps, first adding a binary operation 
taking a rot and a tri and yielding a tri, with +ᵥ as 
notation; then we formally define an add_action and show
that it satisfies the axioms for an additive action. 

has_vadd rot tri
~~~~~~~~~~~~~~~~

TEXT. -/

-- QUOTE:
-- view mul action, mul_rot_tri, as an additive action
-- a rotation "adds itself" to any tri to rotate it thusly

-- We need additive action, borrow mult version (hack)
def add_rot_tri := mul_rot_tri
instance : has_vadd rot tri := ⟨ add_rot_tri ⟩ 

-- Now we've got the "action"

-- QUOTE.

/- TEXT:

add_action rot tri
~~~~~~~~~~~~~~~~~~~

TEXT. -/

-- QUOTE:
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

-- QUOTE.

/- TEXT: 

Yay. We're now able to prove that triangles for a torsor
for our additive group of rotations. 

add_torsor rot tri
~~~~~~~~~~~~~~~~~~

TEXT. -/

-- QUOTE:
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
-- QUOTE.

/- TEXT: 

Programming
-----------

We can now perform interesting computations specified in 
the mathematical language of the domain.
TEXT. -/

-- QUOTE:
#reduce r120 +ᵥ r240 +ᵥ -r0 +ᵥ -r120 +ᵥ r0 +ᵥ tri.t0  -- five costly actions (+ᵥ)
-- r120 acting on the result of r240 acting on the result of ... r0 acting on t0
-- QUOTE.

/- TEXT:
If actions are expensive, and you need to apply multiple actions, the structure
we've created makes it possible to *compute* the net action and to apply it only
once with a guarantee that the result will be the same.
TEXT. -/

-- QUOTE:
#reduce r120  + r240  -  r0  -  r120  + r0 +ᵥ tri.t0  -- add in group, then just one!
-- the sum of r120 and r240 and ... acting on t0.
-- QUOTE.


/- TEXT:
Discussion
----------

Under construction.

Now we have a simple but beautiful and useful new arithmetic 
and mathematical architecture. The architectural components 
are a collection of *points* and a collection of *actions* 
corresponding to differences between points. In our running
example, the collection of actions is rot, and it is a group;
and the collection of points is tri. In addition, we have a
set of essential operations:

- addition of actions to produce resulting actions (+ or -)
- actions acting on points to produce new points (+ᵥ)
- differences of points yielding new actions (-ᵥ)

Finally we have the torsor axioms. 

- ∀ (p1 p2 : Point), (p1 -ᵥ p2) +ᵥ p2 = p1
- (∀ (g : Group) (p : Point), g +ᵥ p -ᵥ p = g)

The first axiom insists that adding the difference 
between two points to the second point must get you
back to the first point. To visualize p1 -ᵥ p2, put 
an arrowhead pointing to p1 then drag a line to p2. 
That arrow is a visualization of the difference. A
key idea is that you can move that arrow around, to
put its tail at any point. If you leave it right at
p2, then it must point right back to p1.  

The second axiom insists that if you subtract any 
point p from the result of applying an action g to 
p then the difference between these points must be 
just g.

An archictural template
~~~~~~~~~~~~~~~~~~~~~~~~

This structure combines a torsor of points with the 
collection of differences between points. Each such 
difference, in turn, acts on any given point through 
addition of itself to that point, thereby displacing
the point by exactly the difference it represents.   

Role of origin
~~~~~~~~~~~~~~

The end result is that the structure of differences
also maps the torsor of points as long as one chooses
an origin point from which the actions reach all the 
other points. Because all three points in our example
algebraic structure look the same, it doesn't matter
which we pick as an origin. The differences give us a
kind of *coordinatization* of the points relative to
a *non-canonical* (arbitrary) choice of origin point.    

We can lay down the structure of the differences 
g : G, by placing the zero difference at any origin 
point o : P, and letting every other point be mapped
by its displacement from that origin. One ends up 
with a "G map" of all points relative to that origin. 

Path Forward
~~~~~~~~~~~~

Our plan is to enrich the architecture we now have
in hand. One key enrichment will be to replace mere
groups of transformations with vector spaces, where
each vector acts on any given point by addition of
itself to the point. The corresponding point torsors
are then affine spaces. To understand vector spaces 
one in turn needs concepts such as fields and rings,
which extend groups with additional structure. 

Briefly stated, a ring is a *commutative* additive 
group (+) together with an associative multiplication
operator satisfying the usual left/right distributive
laws. In a field, there are multiplicative inverses, 
as well, except for at 0.

A vector space has its coefficients from a field. A
slightly weaker structure is called a module. It has
its coefficients from a ring. Modules thus generalize
from vector spaces by relaxing the requirement for
multiplicative inverses (thus division) of actions. 

`Modules <https://www.youtube.com/watch?v=IvukAijXgLE>_`

To be sure that we've given modules their due, we will
cross through them on our way to replacing the rot group
in our example so far with a one dimensional vector space 
over a (coefficient) *field*, K. The corresponding point
torsor will then be the corresonding affine space.  
TEXT. -/
