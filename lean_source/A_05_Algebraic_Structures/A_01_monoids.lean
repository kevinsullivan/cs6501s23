import algebra.group

/- TEXT:
*******
Monoids
*******

In this section, we'll analyze and use the definition of monoids provided
by Lean's *mathlib*. 

Extended Example
----------------

As an exceptionally simple example, we'll define an instance of this 
concept where the elements of a multiplicative monoid are *rotations* 
of an equilateral triangle that leave its vertices pointing in the 
same direction as the original. We call such rotations *symmetries*
of an equilateral triange.  

Think of such a triangle with a black dot marking the top vertex when
the triangle is in an un-rotated state. The symetries are rotations
that leave the rotated triangle sitting right on top of where it was
in its unrotated state. These are rotations by 0 degrees, which 
leaves the dot where it is; by 120 degrees, which rotates the dot by one
vertex counterclockwise; and by 240 degrees, which rotates the dot two 
vertices counterclockwise. Rotating by 360 degrees leaves the dot exactly 
where it started, and so is equal to the zero rotation. 

These are all of the *rotational symmetries* of an equilateral triangle. 
We'll call them *r0*, *r120*, and *r240*. Again these are the *elements* 
of our monoid, well call it *rot_sym_eqtri*, short for the *rotational
symmetries of an equilateral triangle*.

To be a monoid we also need an associative operator that takes any two 
monoid elements and returns another monoid element. Our operator will
work by *composing* translations, and we'll use multiplicative notation
for this operation. As an example, if we compose r120 with r120 we get
a rotation by 240 degrees, which is r240; composing r240 and r120 is 
rotates by 360 degrees giving back the original triangle, and so is
equal to r0. It's a simple exercise to write out the *multiplication
table* for this operator.

Finally we need our set of elements to includes an identity element,
e, that when composed with any element, r, just yields r. Clearly
r0 serves this purpose. 

Elements, Operation, Proofs
---------------------------

To formally specify our monoid of rotational symmetries of a regular
triangle as a monoid, we'll need to represent the set of rotations
and the composition operation, and we'll need to prove that these
components satisfy the monoid laws.
TEXT. -/

-- QUOTE:
-- We represent the set of monoid elements (rotations) as a type
inductive rot_sym_eqtri 
| r0
| r120
| r240

open rot_sym_eqtri

-- We represent the operation as a binary operation on this
def rot_mul : rot_sym_eqtri → rot_sym_eqtri → rot_sym_eqtri 
| r0 r0 := r0
| r0 r120 := r120
| r0 r240 := r240
| r120 r0 := r120
| r120 r120 := r240
| r120 r240 := r0
| r240 r0 := r240
| r240 r120 := r0
| r240 r240 := r120

-- We need a proof that r0 is an identity for this operation

theorem rot_left_ident : ∀ (r : rot_sym_eqtri), rot_mul r0 r = r  :=
begin
assume r,
cases r,
repeat {exact rfl,}
end 

theorem rot_right_ident : ∀ (r : rot_sym_eqtri), rot_mul r  r0 = r :=
begin
assume r,
cases r,
repeat {apply rfl},
end 

-- And we need a proof that the operation is associative

theorem rot_mul_assoc : 
  ∀ (e1 e2 e3 : rot_sym_eqtri), 
    rot_mul (rot_mul e1 e2) e3 = rot_mul e1 (rot_mul e2 e3) :=
begin
assume e1 e2 e3,

cases e1,
repeat { 
  cases e2,
  repeat { 
    cases e3,
    repeat {exact rfl}},  
  },
end 

-- QUOTE.

/- TEXT:
Monoid typeclass
----------------

That's all we need to have a monoid. Next we assemble these 
elements into an instance of Lean's monoid typeclass. Once we
do that, we'll benefit from all of the machinery (including 
notations and other operations) that come Lean's monoid and
its underlying typeclass definitions. So let's look to see
exactly what's needed to create our own monoid instance. 
Here's Lean's definition of monoid.
TEXT. -/

-- QUOTE:
#check @monoid
/-
class monoid (M : Type u) extends semigroup M, mul_one_class M :=
(npow : ℕ → M → M := npow_rec)
(npow_zero' : ∀ x, npow 0 x = 1 . try_refl_tac)
(npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x . try_refl_tac)
-/
-- QUOTE.

/- TEXT:
We see that a monoid on a carrier set, *M* (here of rotations), will
extend semi-group and mul_one_class typeclasses, so we'll need to go
look at those. The typeclass itself requires an operation n_pow, which
will be defined recursively as applying a given operation *n* times. 
The proofs require base and recursive step cases, which will be given
by the base and inductive rules of the given function. Let's ignore the
details of notation for now. What's important to know is that these
proofs are given values here that will be computed automatically
when a definition of npow is actually given.  

The *major* insight to gain from this definition is that, to define 
a monoid typeclass instance, we need to already have instances of 
Lean's semigroup and mul_one_class typeclasses. So Let's see what 
we need for those, digging down until we reach simplest typeclasses. 
We'll then build our monoid typeclass instances in a bottom-up
fashion. 

Semigroup
---------
TEXT. -/

-- QUOTE:
#check @semigroup
/-
class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
-/
-- QUOTE.

/- TEXT: 
We see that to define a semigroup instance we'll need an instance
of has_mul, so let's look at that. 
TEXT. 

has_mul
-------

TEXT. -/

-- QUOTE:
#check @has_mul
/-
class has_mul      (α : Type u) := (mul : α → α → α)
-/
-- QUOTE.

/- TEXT:

has_mul instance
----------------

Hooray, we have everything we need to define an instance of this
typeclass, namely just a multiplication operator (mul) for objects
in our monoid. That operator is rot_mul. (Note that you can define
typeclass instances without giving them names, which is typical.)
TEXT. -/

instance : has_mul rot_sym_eqtri  := ⟨ rot_mul ⟩ 

/- TEXT:

You see here the use of angle-brackets to specify the field 
values of a given structure. It's easier to use than has_mul.mk. 

semigroup instance
------------------

Now we've got what we need to specify a semigroup typeclass
instance, which simply adds the constraint (in the form of a
proof) that the operator be associative.
TEXT. -/

-- QUOTE:
instance : semigroup rot_sym_eqtri := ⟨ rot_mul, rot_mul_assoc ⟩ 

#check @mul_one_class

-- QUOTE. 

/- TEXT:
mul_one_class instance
----------------------

To complete a typeclass instance for monoid, we also need an instance
for mul_one_class, and as we'll now see, that in turn requires 
instances of has_one and has_mul. We aready have an instance of has_mul,
so all we need to define now is has_one, which identities the identity
element in the monoid, which will then be denoted by *1*. 
TEXT. -/

-- QUOTE:
#check @mul_one_class
#check @has_one
#check @has_mul 

/-
class mul_one_class (M : Type u) extends has_one M, has_mul M :=
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)

class has_one      (α : Type u) := (one : α)
-/

instance : has_one rot_sym_eqtri := ⟨ r0 ⟩ 

instance : mul_one_class rot_sym_eqtri := 
⟨  
  r0,
  rot_mul,
  rot_left_ident,
  rot_right_ident,
⟩ 

-- QUOTE. 

/- TEXT:

Yay. We can now assemble our monoid instance. 
TEXT. -/

-- QUOTE:

def rot_npow : ℕ → rot_sym_eqtri → rot_sym_eqtri 
| 0 x := 1
| (nat.succ n') x := rot_mul x (rot_npow n' x)



instance : monoid rot_sym_eqtri := 
⟨
  rot_mul,
  rot_mul_assoc,
  1,
  rot_left_ident,
  rot_right_ident,
  rot_npow,
⟩ 
-- QUOTE. 

/- TEXT:
What we get
-----------

Having defined the monoid of rotational symmetries of a 
regular triangle, we gain some real benefits. First, we
get to use the notations (namely 1 and *) associated with
the monoid identity and operator. Second, we can of course
now define another version of foldr that takes a Lean
monoid as an argument and extends its binary operator
to n-ary, taking an arbitrary number of arguments in a
list. 
TEXT. -/

-- QUOTE:

-- Notations!
#reduce (1 : rot_sym_eqtri)
#reduce (r120 * 1)
#reduce (r120 * r120)

-- foldr using monoid notation
def foldr {α : Type} [monoid α] : list α → α
|  list.nil := 1
| (h::t) := h * foldr t

#reduce foldr []
#reduce foldr [r120,r120]
#reduce foldr [r120,r120,r120]

-- QUOTE.

