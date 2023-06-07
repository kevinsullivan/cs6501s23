import linear_algebra.affine_space.basic
import .A_04_torsors
import group_theory.group_action
import data.real.basic
import algebra.direct_sum.basic

/- TEXT: 

*************
Affine Spaces
*************

While physics and mathematics are usually taught from the
perspective of vector spaces, the beauty of torsors is that 
they allow us to represent *points*, not just differences,
or vectors, between points. Torsors give us an *essential*
mathematical structure for representing *physical* spaces,
comprising both points, e.g., in time, and *differences*,
constituting vectors each acting by points by displacement.

We thus have an algebraic structure in which, for example, 
we can talk about points in 1D or 3D physical spaces (such 
as a point that some robot inhabits), as well as vectors,
comrising differences between points, that *act* on points,
again by displacing, or*translating* them. 

Vectors in our 3-dgeometric space represent displacements: 
differences between points in space. Vectors our idealied 
1-d linear model of time are differences between points in
time. Vectors represent temporal *durations* and spatial 
*displacements*; but the mathematics now let's us model the
points as separate, first-class entities. 

In this chapter we'll formalize these abstractions and show
how to enforce the requisite type distinctions between points
and vectors. while *inheriting* a full affine space structure
on these new types. 

The need for such a structure springs from the possibility of
affine-algebraic, physical-layer type errors in computations in
cases where the carrier sets of point and vector space typeclass
instances coincide: e.g., where both the vector and point types
simply are the rationals, ℚ. 

What we have then is an example of lossy refinement. Distinctions 
between values representing points and vectors are lost to Lean's 
type system. All rational computations are allowed, some of which
are not allowed at the affine/physical level. Example: if points
are just rationals, they can be added together, but doing that has 
no defined affine/physical-level meaning.  

Introduction
------------

Some redundancy here.

A torsor whose actions (via -ᵥ) form a vector space is known 
as an *affine space*. To have a vector space, the associated
scalars must form a *field*. That means scalars have inverse;
thus scalar division, thus scalar fractions; and therefore via 
scalar multiplication by scalar fraction we have *fractions of 
actions* (i.e., of vectors) as well. 

As an example, we'll first consider a one-dimensional torsor 
whose points correspond to, and that we represent by, rational 
numbers understood to be lacking a distinguished zero or origin. 
Point differences (-ᵥ), on the other hand, are understood to be 
rational numbers: elements of ℚ.  

To see what can go wrong, suppose p is a point representedby the
rational 1/2 and v is a vector, literally a rational, namely 1/4. 
The expression v + p represents the point arrived at by translating
p *in the direction and by the magnitude* of v. 

Selecting the rationals to represent points was convenient, as we
can now *compute* what has to be the resulting point (for all the
algebra to work out): namely the point represented by the rational 
number, 1/4 + 1/2 = 3/4.  

However if we replace p by rational 1/2 and then compute p + p 
as rational 1/2 + 1/2, we get a result, but it's not meaningful
in affine algebra. We insist that it should produce a type error, 
even though it makes sense to add the underlying rational numbers. 

The trick, as we'll see, is to define a new type for points,
represented by and thus isomorphic to but distinct from ℚ, 
and subject to be acted on additively by ℚ-valued vectors. 
Then we *lift*, from Lean's library of typeclass instances for 
the rationals, the structures needed for our points to define
a torsor over ℚ-valued vectors. Voila, a typed affine space. 

In other words, we'll show how we can use types and type 
checking in Lean to enforce the axioms/constraints of affine
algebra even though under the hood we might be representing
both points and vectors as values of the same type.  

Example
-------

We will represent the physical dimension of time as a torsor of 
points in time, isomorphic to the rationals, ℚ; over a rational 
vector space of differences, which we'll call durations in time.
We seek a type-system-enforced affine algebra in which to write
computations in this model of points and durations in time. 

For example, if pa and pb are points in time, then dt = pa -ᵥ pb 
must be a duration (vector), and dt +ᵥ pb = pa must always be true.
Suppose pa = 1PM and pb = 3PM. Then dt = (1 - 3) hr = -2 hr. If we
add -2hr to 3PM we get back to 1PM. It all works and makes sense.

What we want to help programmers avoid are errors such as writing
x = pa + pb. Adding points, such as 1PM and 3PM, just doesn't make
any sense at all. Yet if we equate the type of points with ℚ then 
we will be able to write such sums and they will compute. 

The conclusion is that while we might want to represent *abstract* 
points and vectors as rational numbers, we don't want to treat them 
rationals. Points pa and pb can be subtracted to get a difference. 
It is a vector. As such it can be multiplied by a scalar. And it is
here and only here that rationals appear in our final abstraction of
time as a (rational) affine space.

Weakly Typed
------------
 
Points
~~~~~~

We will represent our 1-d space of points in time by rationals. We
do not treat the rational number, 0, as being special. There is no
distinguished origin in classical time. We will represent durations
as vector differences between such points. What can go wrong?

One approach is to define type, *pnt* (for "point"), as just another
name for ℚ. In Lean this can be done using *abbreviation.* In this
example, we'll see that we can not only add points but also treat
them as vectors, neither of which we want to be permitted.

To begin, we'll give a name, K, to whatever scalar field we choose
to use. In this chapter, we'll set it to ℚ, but in principle it can
change, e.g., to ℝ. 
TEXT. -/

-- QUOTE:
abbreviation K := ℚ            -- abstract field to make it easy to change
-- QUOTE. 

/- TEXT:
Now we'll present our first try at an affine space abstraction
in which only affine operations are defined, and no ill-formed
expressions are accepted. We'll use Lean's *abbreviation* keyword
to define pnt as being identical to the type, K, which in turn is
identical to the type ℚ; so writing pnt will be exactly the same
as writing ℚ. 
TEXT. -/

namespace borked
-- QUOTE:

abbreviation pnt := K           -- represent points by field values
def pnt1 : pnt := (1/2:K)       -- a point represented arbitrarily by 1/2 

-- this approach does not rule out bad expressions
def bork := pnt1 + pnt1         -- oops, point-point addition makes no sense
def brok := pnt1 +ᵥ pnt1        -- oops, treating point as vector is not good
-- QUOTE.
end borked


/- TEXT:
Unfortunately, because this approach makes pnt exactly the 
same type as ℚ, all operations on rationals can be applied to 
values of this *point* type. That includes point-point addition, 
which we've already noted makes no physical sense. 

Rather, what we'll need to do is to introduce a new type: one 
that's isomorphic to the rationals but on which we will define
only those operations that make sense given our interpretation
of pnt as the type of elements in a torsor. 

In Lean, defining a new type name using *def* actually creates
a distinct type. So we will try that now. 
TEXT. -/

namespace borked2
-- QUOTE:
def pnt := ℚ
def pnt1 : pnt := (1/2:ℚ)
def bork : pnt := pnt1 + pnt1  -- oops, operation not defined
def brok : pnt := pnt1 +ᵥ pnt1 -- oops, operation not defined
-- QUOTE.
end borked2

/- TEXT:
So now we've got a new type, isomorphic to ℚ, but lacking 
any of the structure (including operations) defined for ℚ
in the Lean libraries. Do we now have to redefine all of 
those structures for our pnt type? The answer is no, we can
*lift* the structures defined for ℚ that we want defined 
for our pnt type using @derive.
TEXT. -/

namespace borked3
-- QUOTE:
#check add_torsor ℚ 
@[derive [add_torsor ℚ]] def pnt : Type := ℚ
def pnt1 : pnt := (1/2:ℚ)
def vec := pnt1 -ᵥ pnt1   -- oh, hooray, allowed
def nope := pnt1 + pnt1   -- oh, hooray, disallowed
#check vec                -- oops, just bare rationals
-- QUOTE.
end borked3

/- TEXT:
We've now got our torsor -ᵥ operation defined for points, 
but the results of this operation are still bare rationals,
not elements of a vector type. Let's fix that next. 

Vectors
~~~~~~~

Given that differences between points still have the type 
of bare rationals, we can use our vector object whereever 
any rational is expected, and we can use any rational, no 
matter what it actually means, as a vector in our physical
and geometric computations. That is not good enough. 

The solution, again, is to define a vector type isomorphic
to, but distinct from, ℚ, while lifting the vector space
structure from ℚ to our new *vec* type. Then we will use
this new type as the *vector space* type for our torsor of
points. 

As an aside: Recall that Lean doesn't provide vector_space 
as a typeclass; rather one uses module with a scalar field 
to acheive this result. So we will need to lift the module
structure from ℚ to our new *vec* (for vector) type. We will
also need to lift add_comm_monoid and add_group structures
for everything to work. Note how we do this by deriving from
a list of structures already defined in the libraries for ℚ.
Further, not that deriving from has_repr allows Lean to print
out pnt and vec values in the same way it'd print rationals. 
TEXT. -/

-- QUOTE:

-- First we define our vector type with the right structures
@[derive [add_comm_monoid, add_group, module K, has_repr]] def vec : Type := K

-- Now we define a torsor over this vector space
@[derive [add_torsor vec, has_repr]] def pnt := K
-- QUOTE. 

/- TEXT:
Affine algebra
~~~~~~~~~~~~~~

With that we've constructed a typechecked affine algebra of the kind
we've sought. The following examples exhibit uses of the torsor and 
vector space operations for the case where points, vectors, and scalars 
are all (virtual copies of) ℚ. 
TEXT. -/

-- QUOTE:

-- define several points, initialized, as we see, by elements of K. 
def pnt1 : pnt := (1/2:K)
def pnt2 : pnt := (3/2:K)

-- We can confirm that supported operations work correctly
def vec1 := pnt2 -ᵥ pnt1                -- YAY, point-point subtraction 
def pnt3 := vec1 +ᵥ pnt2                -- YAY, action of vector on point
def pnt4 := ((2/3:ℚ) • vec1) +ᵥ pnt2      -- YAY, scalar mul (•) yields vec

-- The resulting values are correctly computed?
#eval vec1    -- expect 1
#eval pnt3    -- expect 5/2
#eval pnt4    -- expect 2/3 + 3/2 = 13/6

-- And physically meaningless operations produce type errors 
#check pnt1 + pnt1              -- oops, type error, can't add points
def vec' := pnt2 - pnt1         -- oops, type error, use torsor -ᵥ operation
def pnt' := pnt2 + vec1         -- oops, type error, use vec-point +ᵥ
def pnt'' := pnt2 +ᵥ vec1       -- oops, vector arg has to come first
def pnt''' := ((2/3:ℚ) * vec1) +ᵥ pnt1  -- oops, first term is ℚ not vec
-- QUOTE. 


/- TEXT:
We thus now have an algebraic structure that we set out to
construct at the beginning of this class: a statically type
checked, and computable affine space abstraction. As a final
detail, we note that could have used mathlib's *affine_space*
typeclass in lieu of add_torsor, as they mean the same thing.


affine_space V P
----------------

Still a bit under construction. Just one idea. 

In Lean, *affine_space V P*, where *V* is the type of
vectors and P is the type of torsor elements, or points, 
is just a *notation* for *add_torsor V P.* 

`affine_space <https://leanprover-community.github.io/mathlib_docs/linear_algebra/affine_space/basic.html>`_
TEXT. -/

-- QUOTE:
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
-- QUOTE.

/- TEXT:
What that means is that we could have declared our torsor as
an actual affine_space, with no effect on the meaning of our
definitions. 
TEXT. -/

-- QUOTE:
-- @[derive [add_torsor   vec, has_repr]] def pnt := K
-- @[derive [affine_space vec, has_repr]] def pnt := K
-- QUOTE. 

