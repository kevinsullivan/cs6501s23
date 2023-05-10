
*************
Affine Spaces
*************

While physics and mathematics are usually taught from the
perspective of vector spaces, the beauty of torsors is that 
they allow us to represent *points*, not just differences,
or vectors, between points. Torsors give us an *essential*
mathematical structure for representing *physical* spaces,
including points in time and in the geometric spaces that
we inhabit.  

We thus have an algebraic structure in which, for example, 
we can talk about points in 1D or 3D physical spaces as well
as vectors that *act* upon points (such as the location of 
a robot or any other object) by *translating* them. Vectors
in time represent directed *durations*, while  vectors in 
geometry  represent directed spatial *displacements*.

In this chapter we'll formalize these abstractions and show
how we can use them to represent type-correct computations 
in such physical spaces.

Introduction
------------

A torsor whose actions (via -ᵥ) form a vector space is known 
as an *affine space*. To have a vector space, the associated
scalars must form a field. That means scalars have inverses,
and so we have scalar division, thus scalar fractions, and 
therefore we also have all *fractions* of vectors, as well
(via scalar multiplication by scalar fractions). 

As an example, we'll first consider a one-dimensional torsor 
whose points correspond to the rational numbers. Differences 
(-ᵥ) will be computed by rational number subtraction, so vectors
will also correspond to rational numbers. 

We'll see that if we use bare rational numbers to represent 
points and vectors, we'll be able to perform physically and
mathematically meaningless operations, such as the addition
of two points. We'll then see how to use Lean's type system
to distinguish between rationals representing points and those
representing vectors, so as to be assured that type correct
expressions are also physically and mathematically correct.  

For example, if p and v are rationals representing the *point* 
1/2 and the vector, 1/4, we want to allow p + v, resulting in the 
point 3/4. However, the expression p + p makes no physical sense, 
and so should produce a type error, even though it makes sense to 
add the underlying rational numbers. 

The trick, as we'll see, is to define new types for points and
vectors that are isomorphic to and represented by the rationals,
and then to *lift*, from the rationals, only those operations 
and structures that are necessary and sufficient to define an
affine space of points over a vector space of actions. 

In other words, we'll show how we can use types and type 
checking in Lean to enforce mathematical consistency in 
expressions meant to represent geometric and other physical
computations involving affine spaces and their associated
vector space operations. 

Example
-------

Suppose we want to model points in time and differences between
them, also called durations, representing both by rational numbers
(with which we can compute automatically). The points will form a
torsor over the vector space of differences (vectors, durations), 
which will thus also be represented by rational numbers. In this
vector space, the scalar field will also be the rationals. 

As a concrete example, if we represent noon as a point in time,
n = 0/1, and a duration of one hour as the rational number, h = 1, 
then we can represent the time, one thirty, as n +ᵥ (3/2 * h). That
is, the point, noon, plus the duration, one and a half hours. What
we don't want to allow is an expression such as n + n. Noon plus
noon makes no sense whatsoever and so should be ruled as a type
error. 

So let's look at a few false starts on such an algebra, and then
we'll settle on a satisfactory design. 

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

.. code-block:: lean

  abbreviation K := ℚ            -- abstract field to make it easy to change

Now we'll present our first try at an affine space abstraction
in which only affine operations are defined, and no ill-formed
expressions are accepted. We'll use Lean's *abbreviation* keyword
to define pnt as being identical to the type, K, which in turn is
identical to the type ℚ; so writing pnt will be exactly the same
as writing ℚ. 

.. code-block:: lean

  
  abbreviation pnt := K           -- represent points by field values
  def pnt1 : pnt := (1/2:K)       -- a point represented arbitrarily by 1/2 
  
  -- this approach does not rule out bad expressions
  def bork := pnt1 + pnt1         -- oops, point-point addition makes no sense
  def brok := pnt1 +ᵥ pnt1        -- oops, treating point as vector is not good

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

.. code-block:: lean

  def pnt := ℚ
  def pnt1 : pnt := (1/2:ℚ)
  def bork : pnt := pnt1 + pnt1  -- oops, operation not defined
  def brok : pnt := pnt1 +ᵥ pnt1 -- oops, operation not defined

So now we've got a new type, isomorphic to ℚ, but lacking 
any of the structure (including operations) defined for ℚ
in the Lean libraries. Do we now have to redefine all of 
those structures for our pnt type? The answer is no, we can
*lift* the structures defined for ℚ that we want defined 
for our pnt type using @derive.

.. code-block:: lean

  #check add_torsor ℚ 
  @[derive [add_torsor ℚ]] def pnt : Type := ℚ
  def pnt1 : pnt := (1/2:ℚ)
  def vec := pnt1 -ᵥ pnt1   -- oh, hooray, allowed
  def nope := pnt1 + pnt1   -- oh, hooray, disallowed
  #check vec                -- oops, just bare rationals

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

.. code-block:: lean

  
  -- First we define our vector type with the right structures
  @[derive [add_comm_monoid, add_group, module ℚ, has_repr]] def vec : Type := ℚ
  
  -- Now we define a torsor over this vector space
  @[derive [add_torsor vec, has_repr]] def pnt := K
  
  -- With that we can define a few points
  def pnt1 : pnt := (1/2:K)
  def pnt2 : pnt := (3/2:K)
  
  #eval pnt1
  
  -- We can confirm that supported operations work correctly
  def vec1 := pnt2 -ᵥ pnt1                -- YAY, point-point subtraction 
  def pnt3 := vec1 +ᵥ pnt2                -- YAY, action of vector on point
  def pnt4 := ((2/3) • vec1) +ᵥ pnt2    -- YAY, scalar mul (•) yields vec
  
  -- The resulting values are correctly computed
  #eval vec1    -- expect 1
  #eval pnt3    -- expect 5/3
  #eval pnt4    -- expect 2/3*1 + 3/2 =
  
  -- And physically meaningless operations produce type errors 
  #check pnt1 + pnt1              -- oops, type error, can't add points
  def vec' := pnt2 - pnt1         -- oops, type error, use torsor -ᵥ operation
  def pnt' := pnt2 + vec1         -- oops, type error, use vec-point +ᵥ
  def pnt'' := pnt2 +ᵥ vec1       -- oops, vector arg has to come first
  def pnt''' := ((2/3:ℚ) * vec1) +ᵥ pnt1  -- oops, first term is ℚ not vec

affine_space V P
----------------

-- Still under construction. 

In Lean, *affine_space V P*, where *V* is the type of
vectors and P is the type of torsor elements, or points, 
is just anotation for *add_torsor V P.* 

`affine_space <https://leanprover-community.github.io/mathlib_docs/linear_algebra/affine_space/basic.html>`_

.. code-block:: lean

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

What that means is that we could have declared our torsor as
an actual affine_space, with no effect on the meaning of our
definitions. 

.. code-block:: lean

  -- @[derive [add_torsor   vec, has_repr]] def pnt := K
  -- @[derive [affine_space vec, has_repr]] def pnt := K

