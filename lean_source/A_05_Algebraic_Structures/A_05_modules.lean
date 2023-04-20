import .A_04_torsors
import algebra.module

/- TEXT:
We've now undertood what it means to be a torsor over a 
group, with a concrete example of a torsor of triangles 
over a group of rotational symmetries. In this chapter, 
we strengthen this concept by upgrading a mere group of
differences to a *module*, from which it's a short leap
to a *vector space*. 

Once we get there, we will have a formalization of an 
*affine space*, which is simply a torsor of points over 
a *vector space* (instead of just a group). That is, we'll 
have a structure in which *vectors* act on *points* by 
translating them, in a way that satisfies the torsor axioms. 

Such a space is basically a coordinate-free set of points,
that we can use to represent positions in classical space
and time (physics!), along with a transformation group (and
not just a group but a vector space) of actions. 

Such an affine space can be visualized as a Euclidean space,
familiar even from high-school algebra, without an origin or
coordinate system, and also without the added structure of a
Euclidean norm. 

Informal Introduction
---------------------

The path to vector spaces passes through the very important
concepts of a *module*. So before going further, let's get a
sense of the path.

vector space
~~~~~~~~~~~~

We've started with a torsor over a group. A *vector space* in
turn has a richer structure than a mere group. It is a set of 
objects that has a additive *and commutative* group structure, 
thus addition and subtraction operations (v₁ + v₂ and v₁ - v₂), 
where (v₁ + ∨₂ = v₂ + v₁), but also a *scalar multiplication* 
operation, (k • v), where k ∈ K is an element of a *field, K*. 

field
~~~~~

A field, in turn, has the structure of both an additive and
commutative group, thus (k₁ + k₂) and (k₁ - k₂) operations, 
where (k₁ + k₂ = k₂ + k₁) and a commutative multiplicative 
group, with a commutative (k₁ * k₂) multiplication operation 
(k₁ * k₂ = k₂ * k₁); a division operation, (k₁ / k₂), except
where k₂ = 0, and an identity, 1 . These operations are, in 
turn, required to satisfy the usual distributive laws familiar 
from everyday arithmetic.  Examples of *scalar fields* include
the real number, ℝ, the rationals, ℚ, and the complex numbers, 
ℂ, among others.

axioms
~~~~~~

Vector space axioms, beyond those already inherited from monoid 
(associative addition, additive identity) and group (additive
inverses, thus also subtraction), we require (1) compatibility 
of scalar and field multiplication, k₁(k₂v) = (k₁k₂)v (we omit  
• as a shorthand); (2) distributivity of scalar multiplication 
over vector addition, k (v₁ + v₂) = kv₁ + kv₂; and finally (3),
distributivity of scalar multiplication with respect to field 
addition, (k₁ + k₂) • v = k₁v + k₂v.   

A vector space is then a set of "vector" objects that is closed
under both vector addition and scalar multiplication. If, for 
example, we have a *real (ℝ)* vector space that includes two 
vectors, v₁ and v₂, and if k₁ and k₂ are real numbers, then the
vectors k₁ • v₁, k₁ • v₂, and k₁ • v₁ + k₂ • v₂ are also in the 
vector space.

ring
~~~~

A ring generalizes a field by relaxing the requirements for 
(1) commutativity of multiplication and (2) multiplicative 
inverses. It thus loses division as an operation.  

module
~~~~~~

A module is like a vector space but with a scalar field that
is a ring and not necessarily a field. 

This file defines the typeclass module R M, which gives an 
R-module structure on the type M. An additive commutative 
monoid M is a module over the (semi)ring R if there is a 
scalar multiplication • (has_scalar.smul) that satisfies 
the expected distributivity axioms for + (in M and R) and 
* (in R). To define a module R M instance, you first need 
instances for semiring R and add_comm_monoid M. 

By splitting out these dependencies, we avoid instance loops 
and diamonds.
TEXT. -/