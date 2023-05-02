
/- TEXT: 

ring
~~~~

A ring is a set of values with commutative addition, 
additive inverses and thus subtraction (making it an
additive commutative group), and multiplication, not 
necessarily commutative, where + and * satisfy the 
usual associativity and distributivity axioms.

A nice example of a ring is the integers. It obviously
has commutative addition, negation and thus subtraction,
and multiplication, but lacks multiplicative inverses and
thus division. Integer multiplication is commutative, so
in this special case we have a *commutative ring*. 

scalar multiplication
~~~~~~~~~~~~~~~~~~~~~

A geometric interpretation of scalar multiplication is 
that it "scales" a module element (such as a vector) by 
an amount given by a scalar. Maybe they should have been 
called "scalers!"

In fact, to form a module, we don't even need a group
of actions, just an additive commutative monoid, M, a 
type of scalars, R, and scalar multiplication, •, of 
monoid elements by scalars. The monoid element serve 
as vector-like objects, and the scalars as scalars in
typical scalar-vector multiplication.  

putting it together
~~~~~~~~~~~~~~~~~~~

With the right pieces in place, we form a module structure on
a set of vector-like objects, M, and a set of scalar objects,
R, by instantiating the typeclass *module R M*. 
TEXT. -/

-- broken variables 
variables
  (M : Type)  [acm: add_comm_monoid M]
  (R: Type)   [sr: semiring R]
#check module R M


/- TEXT: 

vector space
~~~~~~~~~~~~

A vector space, in turn, has a slightly richer structure 
than a mere module. In particular, the scalars now have to
form not only a ring but a *field*. 

field
~~~~~

A field (e.g., of scalars) has the structure of both an additive, 
commutative group, with + and -, and of a multiplicative group, 
with * and /, the zero element being excepted. These operations 
must satisfy the usual distributive and associative laws familiar 
from everyday arithmetic.  Examples of *scalar fields* include 
the real numbers, ℝ, the rationals, ℚ, and the complex numbers, 
ℂ, among others. Do take a moment to think through what it means
that ℝ with the usual +, -, *, / is a *field*. 

vector space axioms
~~~~~~~~~~~~~~~~~~~

Vector space axioms, beyond those already inherited from monoid 
(associative addition, additive identity) and group (additive
inverses, thus also subtraction), we require the following:

- compatibility of scalar and field multiplication, i.e., k₁(k₂v) = (k₁k₂)v (we omit • as a shorthand) 
- distributivity of scalar multiplication over vector addition, k (v₁ + v₂) = kv₁ + kv₂
- distributivity of scalar multiplication over field addition, (k₁ + k₂) • v = (k₁ • v) + (k₂ • v).   

A vector space is then a set of "vector" objects that is closed 
under both vector addition and scalar multiplication. If, for example, 
we have a real vector space (with scalars from ℝ) that includes two 
vectors, v₁ and v₂, and any scalars k₁ and k₂ ∈ ℝ, then the vector,  
k₁v₁ + k₂v₂ (•/smuls) is also in the vector space.

module
~~~~~~

A module is like a vector space but with scalars that come
from a mere *ring* and not necessarily from a *field*. Every 
field is an extension of a ring, so every vector space is a 
module, but not every ring is a field, so not every module 
is a vector space.

ring
~~~~

A ring is a generalization of a field that no longer insists
on multiplicative inverses, and so while +, -, and * remain,
a ring can lack division, /. 

Two examples of rings are integers and polynomials. You can
multiply, add, and subtract integers and polynomials, and
get integers and polynomials back, resp. However, you can't
divide integers and (always) get integers, and similarly you
can't divide polynomials and (always) get polynomials. These
sets and operations form rings but not fields. By contrast,
we do have multiplicative inverses in the reals, rationals, 
and complex numbers. These sets and their usual operations 
form not only rings but fields.  

Scalar multiplication by values from the *ring* of integers
(no division) suggests a module but not a vector space. If
scalar multiplication is by values from the *field* ℝ or ℂ 
or ℚ (satisfying the axioms), with elements from an additive
commutative monoid, then you have a vector space. The vectors 
are the monoid elements and the scalars are from the selected
field.

Please remind yourself at this point that we're talking only
about the algebraic structure of the set of actions. We have
not yet connected any of this back to a torsor of "points" on
which the actions of a given module act. There are just now
two sets involved in representing actions: monoid elements
and scalars. So what you have is a much richer algebra than
just a group; now you have both addition as well as scaling 
of actions!

TEXT. -/

-- QUOTE:
-- module / vector space
  +----------------+
  |                |
  |  +---+  +---+  |
  |  | R |  | M |  | ----- acts on ----> torsor
  |  +---+  +---+  |
  |                |
  +----------------+
-- QUOTE.

/- TEXT: 
R is at least a ring and M is at least an additive
commutative monoid. If R is also a field, then any
(module R M) is also a vector space. In this case, 
its torsor is an affine space where points differ
by these translation actions (a.k.a., "vectors").
TEXT. -/

/- TEXT:

This file defines the typeclass module R M, which gives an 
R-module structure on the type M. An additive commutative 
monoid M is a module over the (semi)ring R if there is a 
scalar multiplication • (has_scalar.smul) that satisfies 
the expected distributivity axioms for + (in M and R) and 
* (in R). To define a module R M instance, you first need 
instances for semiring R and add_comm_monoid M. 

By splitting out these dependencies, we avoid instance loops 
and diamonds.


Aims
----

In our big picture so far, we have an additive group 
of (rot) actions, that act on (tri) points by rotating
them. We also have that differences between points are 
corresponding action (rot) group elements. 

This structure allows us to compose actions (rotations)
using the group (commutative) addition and subtraction 
operations before having them act on points. 

We now want to keep addition, we will relax the need
for additive inverses, but add multiplication of any 
action, m, by any scalar, k, where scalars come from 
a set with its own structure. The intuition is that 
scalar multiplication (•) "scales" any given module 
element. 

The difference between module and vector space is not
in the combination of an additive monoid (or group if
you wish) of actions with scalar multiplication as well,
but rather in the choice of the scalars. If the scalars 
form at least a ring (commutative addition, subtraction, 
and not necessarily commutative multiplication, with the
usual distributive rules) the you have a module. If in
addition, scalars have multiplicative inverses, and thus
division (except by 0), then you have a scalar *field*
(not just a scalar ring); the module becomes a vector
space; and its torsor of points becomes an affine space. 

Our main task now is to upgrade the group to a module
over at least a ring of scalars. We'll set aside the 
points until we're done rediscovering the module. It 
will then be a very short jump to vector spaces: we
will just insist that the scalar ring is actually a 
field. 

implementation
~~~~~~~~~~~~~~

In Lean, a module R M structure is defined by instantiating 
the module R M typeclass. 


The module elements are given by a *monoid,* M. For our
purposes, one can think of M elements as quasi-vectors. As 
an example, our rotations (rot) elements certainly form an
additive monoid, as a substructure of its group structure.
You can even draw rot elements as little semi-circular 
vectory lines with arrowheads; and they add up just like 
vectors do, too. 


To this structure, a module adds a second type, R, of 
so-called scalars, and an operation to multiply scalars
by by monoid (M) elements to produce ("scaled") monoid 
values. The module axioms make everything "linear" by 
enforcing natural distributivity rules when combining
addition, subtraction, multiplication, and sometimes
division *of pairs of scalars* with scalar multiplication 
by of scalars by monoid elements. 

For exampe, it better be the case that (r₁ + r₂) • v = 
(r₁ • v) + (r₂ • v). Be sure you see that the + on the
left is addition of scalars, while the + on the right
is addition of monoid elements (each obtained by scalar
multiplication).


as extending a
monoid than extending a group, and that is what Lean 
does in Mathlib. Think of the monoid elements as being
"quasi-vectors" if you want to keep track of where we
are headed here.  

The monoid structure
gives us associative addition and an identity element. 
We then select a scalar ring or field and define the
scalar muliplication operation taking a scalar and a
monoid element to another monoid element (just like
multiplying a scalar and a vector yields a scaled
vector). 

As stated in the Mathlib documentation, "An additive 
commutative monoid M (remember we dropped the need for
additive inverses and thus subtraction) is a module over 
the (semi)ring R if there is a scalar multiplication • 
(has_scalar.smul) that satisfies the distributivity 
axioms for + (in M and R) and * (in R). 


They
are additive commutative group semi-ring 

`Mathlib documentation <https://leanprover-community.github.io/theories/linear_algebra.html>`_


"This file defines the typeclass module R M, which gives 
an R-module structure on the type M. 



"To define a module R M instance, you first need instances 
for semiring R and add_comm_monoid M. By splitting out 
these dependencies, we avoid instance loops and diamonds."
TEXT. -/

variables (K : Type) [field K]