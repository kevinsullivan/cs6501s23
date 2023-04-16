
import .A_01_monoids
import group_theory.group_action

/- TEXT: 

*************
Group Actions
*************

We now seen that group elements can be understood as
actions that can be performed on some other kinds of
objects. For example, elements of the Lie group, S1,
namely points on the complex unit circle, represent 
rotations of vectors specified by arbitrary complex
numbers. Moreover, every possible degree of rotation
has a corresponding group element. It's a continuous
transformation group. 

By contrast, our group of rotational symmetries of an
equilateral triangle (rotations that put it right back
on top of itself) is hardly continuous. Nevertheless, 
it can be understood as a group of actions, acting on
such a triangle.

More generally, an action acts on something, and in 
general these somethings are not of the same type as
the actions themselves. For example, elements of S1
are *special* complex numbers, lying on the unit circle,
and understood on any arbitrary vector, represented by 
an complex number, by complex number multiplication,
thereby effecting a pure rotation (no dilation) of the
target vector.

We thus now have two types involved: the type of the 
group elements and the type of the objects that the group
elements act upon. In this chapter, we'll use G as the name
of the type of group elements, and α for the type of the 
objects that group elements act on. 

To make the concept of a group action clearer, we'll develop
it in the context of our running example of the rotational 
symmetries of equilateral triangles. What these actions act
on are equilaterial triangles. We'll overload an operation
called smul, introduced by the group_action typeclass, and
denoted g • b to represent the result of applying the action
g to the object b, with a result of the same type b has. As
an example, if b is the triangle rotated 120 degrees then
the result of applying the r120 action to b would be the 
triangle rotated 240 degrees. 

We could define a generalized triangle type, but in this
example, there are only three configurations that we care
about: not rotated, rotated by 120 degrees, and rotated by
240 degrees. That means we can represent this set with a
type, we'll call it tri, with just three values. We'll 
call them t0, t120, and t240.

The concept of a group acting on objects of some type is
fundamental in mathematics. And there's a notation for that.
If g ∈ G and b ∈ α then we can write (g • b) to denote the
result of g acting on b. 

Lean provides this notation through instantiation of its
group_action typeclass. In addition to this notation, this
typeclass requires verification of the two actioms of group
actions, namely that 1 • b = b, and that (g₁ \* g₂) • b =
g₁ • (g₂ • b). 

So, first, the group identity has to act as an identity 
for α. Second, you can compose transformations (g₁ * g₂)
then apply the result to a target, or you can transform 
by g₁ the result of transforming b by g₂, and you'll get 
the same results. 

It's easier to think about sequential application of 
transformations than applications of their compositions, 
but as we'll see, the ability to compose arbitrary 
transforms into reduced transforms will be essential.  

Target Type
-----------
TEXT. -/

-- QUOTE:
inductive tri 
| t0
| t120
| t240
-- QUOTE.

/- TEXT: 
Typeclasses
-----------

To instantiate the group_action typeclass, we'll have to
do so for the group_smul class, providing an implementation
of the *smul* function that computes the results of group
actions; and we'll have to gven proofs of compliance with 
the two axioms. At the end of the chapter we'll introduce
some other examples and emphasize that the step taken in
this chapter has given us a way not only to represent 
but also to apply transformations. The smul operation, •, 
applies a group element representing an operation to a 
given target object, returning its transformed state. 


has_smul
~~~~~~~~

TEXT. -/

-- QUOTE:
/-
@[ext, class]
structure has_smul (M : Type u_1) (α : Type u_2) :
Type (max u_1 u_2)
    smul : M → α → α
-/
-- QUOTE.


/- TEXT:

group_action
~~~~~~~~~~~~
TEXT. -/

-- QUOTE:
/-
universes u_10 u_11

@[ext, class]
structure mul_action (α : Type u_10) (α : Type u_11) [monoid α] :
Type (max u_10 u_11) :=
(    to_has_smul : has_smul α α)
(    one_smul : ∀ (b : α), 1 • b = b)
(    mul_smul : ∀ (x y : α) (b : α), (x * y) • b = x • y • b)
-/
-- QUOTE.


/- TEXT:

Instances
---------

has_smul rot tri
~~~~~~~~~~~~~~~~
TEXT. -/

open rot
open tri

-- QUOTE:
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

-- QUOTE.

/- TEXT: 
mul_action M α 
~~~~~~~~~~~~~~

`mul_action M α` and its additive version `add_action G P` 
are typeclasses used for actions of multiplicative and 
additive monoids and groups; they extend notation classes
`has_smul` and `has_vadd` defined in `algebra.group.defs`;
TEXT. -/
-- QUOTE:

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


-- QUOTE.

/-TEXT: 
Discussion
----------



TEXT. -/


