
import .A_01_monoids

/- TEXT: 

******
Groups
******

In this chapter, we'll turn to a first study of groups. 
Simply put, a group is an algebraic structure that includes 
all of the structure of a monoid with the addition of an
inverse operator. This operator then makes it possible to
define the related notion of division in a group, defining 
*div a b,* usually denoted (a / b), as *(mul a (inv b))*.
We'll be particularly interested in viewing group elements,
of some type, α, as specifying *actions* or *transformations* 
of objects of some other (often the same) type, β. 

Examples
--------

As concrete examples let's consider two groups, one whose
elements represent rotation actions that can be applied to
objects in some 3-D space, and one whose elements represent
translations (straight-line movements) of objects. We'll
look at the concept of a rotation group first.

Rotation groups
~~~~~~~~~~~~~~~

In this view, the multiplication operation of the group is
understood as *composing* actions. If *a1* and *a2* are two 
rotations, for example, then *(a2 \* a1)* is the overall
rotation that results when rotation *a1* is followed by 
rotation *a2*. That every group also has the structure of 
a monoid let's us fold any arbitrary sequence of actions 
to obtain a single resultant action, also in the group. 

The inverse operation of the group is then understood as a
*undo* action, one for each and every action in the group. 
If *a* is 90 degree counter-clockwise rotation in the 2-D
plane, for example, then *a⁻¹* is would be the 90 degree
*clockwise* rotation that undoes the effect of *a*. The 
overall action, *a⁻¹ \* a,* is thus *e*, the action that
performs no rotation at all. 

Translation groups
~~~~~~~~~~~~~~~~~~

As another example of a group, consider a vector space, 
familiar from basic linear algebra. It is a group. The
elements are vectors. A vector, v, acts on an object, p, 
by *translating* it through a straight-line motion by a
distance, and in the direction, of v. Vector addition is 
the (additive) group operator, so *v2 + v1* is the action 
that has the effect of translating an object by v1 then 
by v2. The zero vector is the group identity that leaves
objects unchanged. Finally, the (additive) inverse, -v, 
of a vector, v, undoes the action of v so that the effect
of v + (-v), usually written v - v, does no translation 
at all. It's the zero vector.

Chapter plan
~~~~~~~~~~~~

In the rest of this chapter, we'll work out an extended
example of a formal specification of, and of computation
involving, a small, discrete, finite group, namely the
group of *rotational symmetries* of an equilateral triangle,
In the first section, we'll formalize the rotation group
itself. In the second section, we'll formalize the group
action, of rotations on (representations of) equilateral 
triangles. 

A rotation of this kind rotates an equilateral triangle by 
an amount that makes the resulting triang sit right on top 
of the original equilateral triangle. These are rotations
by 0, 120, and 240 degrees. There are no other rotational
symmetries of such a triangle. 

A group structure on a collection of objects of a given 
type, α, is (typically) specified in Lean by instantiating
the *group* typeclass for α. The group typeclass extends
from several parent typclasses, including monoid, which
reflects the fact that every group with its operator and
identity also satisfies the monoid axioms. 

Groups
------

We'll use the same method as in the last section to analyze
and then provide the values needed to instantiate the group
typeclass for a new type, with three values, representing the
set of symmetry rotations. We'll start top-down, with Lean's 
group typeclass, see what typeclasses it extends, and then
construct the elements needed to instantiate all of these
typeclasses, finally assembing all of these pieces into a
group typeclass instance for our set of rotation-representing
group elements. 

group
~~~~~

Here's the definition of the group typeclass in Lean. It
extends from a (non-mathematically standard) class called
div_inv_monoid. It provides a unary inverse and binary
division operations, with division just multiplication by 
inverse; and associated notations (a⁻¹ and a/b). The group
typeclass then adds a constraint (required proof) that, 
for any a in the group, a⁻¹ is really a left inverse for a. 
TEXT. -/

-- QUOTE:
#check @group
/-
class group (G : Type u) extends div_inv_monoid G :=
(mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
-/
-- QUOTE.

/- TEXT: 

div_inv_monoid
~~~~~~~~~~~~~~

The div_inv_monoid typeclass in turn extends monoid, has_inv,
and has_div. A group is thus automatically a monoid. Instances 
of the has_inv and has_div typeclasses provide unary inverse 
and binary division operations. 
TEXT. -/

-- QUOTE: 
-- What is a div_inv_monoid?
#check @div_inv_monoid
/-
class div_inv_monoid (G : Type u) extends monoid G, has_inv G, has_div G :=
(div := λ a b, a * b⁻¹)
(div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ . try_refl_tac)
(zpow : ℤ → G → G := zpow_rec)
(zpow_zero' : ∀ (a : G), zpow 0 a = 1 . try_refl_tac)
(zpow_succ' :
  ∀ (n : ℕ) (a : G), zpow (int.of_nat n.succ) a = a * zpow (int.of_nat n) a . try_refl_tac)
(zpow_neg' :
  ∀ (n : ℕ) (a : G), zpow (-[1 + n]) a = (zpow n.succ a)⁻¹ . try_refl_tac)
-/
-- QUOTE.

/- TEXT: 

has_inv and has_div
~~~~~~~~~~~~~~~~~~~

TEXT. -/

-- QUOTE:
-- what are has_inv and has_div
#check @has_inv
/-
class has_inv      (α : Type u) := (inv : α → α)

An instance of has_inv holds a single unary operator, inv, 
on group elements of type α, and provides the notation, a⁻¹, 
to mean (inv a). 
-/
#check @has_div
/-
class has_div      (α : Type u) := (div : α → α → α)

An instance of has_div holds a single binary operator, div, 
on group elements of type α, and provides the notation, a/b 
to mean (mul a (inv b)), or (add a (inv b)), depending on
whether one is working with a multiplicative or additive
group. The notion of division is generalized to any group
in this way. 
-/
-- QUOTE.

/- TEXT:
An instance of the has_inv typeclass will have one field
value, a total function from group elements to other group 
elements. In the context of a group, it will be cosntrained
to behave as a genuine inverse operation must: that given 
an element, r, it will return an element r⁻¹, such that
r⁻¹ * r = 1 (the group identity element). 

Of course the * operator will have to have an inverse for
every element of the group. We'll now define an inverse
operation for our rotations and will soon show that it 
satisfies the axioms for being a (left) inverse. 

instances for rot_syms
~~~~~~~~~~~~~~~~~~~~~~

To construct instances, we have to understand their 
constructors. We generally leave structure constructor
names implicit and let Lean fill them is as *mk*. By
#check-ing the type of mk, you see what arguments you 
have to provide, including both data and proofs. Let's 
check the type of div_inv_monoid.mk.
TEXT. -/

-- QUOTE:

#check @div_inv_monoid.mk 
/-
div_inv_monoid.mk :
  Π -- arguments
    {G : Type u_1} 
    (mul : G → G → G)
    (mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
    (one : G)
    (one_mul : ∀ (a : G), 1 * a = a) 
    (mul_one : ∀ (a : G), a * 1 = a) 
    (npow : ℕ → G → G)
    (npow_zero' : auto_param (∀ (x : G), npow 0 x = 1) (name.mk_string "try_refl_tac" name.anonymous))
    (npow_succ' : auto_param (∀ (n : ℕ) (x : G), npow n.succ x = x * npow n x) (name.mk_string "try_refl_tac" name.anonymous))
    (inv : G → G) 
    (div : G → G → G),  -- comma
    auto_param (∀ (a b : G), a / b = a * b⁻¹) (name.mk_string "try_refl_tac" name.anonymous) →
    Π (zpow : ℤ → G → G),
      auto_param (∀ (a : G), zpow 0 a = 1) (name.mk_string "try_refl_tac" name.anonymous) →
      auto_param (∀ (n : ℕ) (a : G), zpow (int.of_nat n.succ) a = a * zpow (int.of_nat n) a) (name.mk_string "try_refl_tac" name.anonymous) →
      auto_param (∀ (n : ℕ) (a : G), zpow -[1+ n] a = (zpow ↑(n.succ) a)⁻¹) (name.mk_string "try_refl_tac" name.anonymous) →
  div_inv_monoid G
-/
-- QUOTE.

/- TEXT:
From the constructor type we can see that we'll need to provide explicit argument 
values for mul, mul_assoc,  one, one_mul, mul_one, and npow, all of which we already
have from our monoid typeclass for rot_syms, as well  as implementations of inv and div, 
and zpow. The last three we need to define. For inv, just work out how the function has 
to behave for each of the three possible inputs (r0, r120, r240). For example, the inverse 
of r120 is r240 because r240 after r120 is not rotation at all. The div function is defined 
in one line in terms of inv. 

The new challenge here will be with zpow. Note that its first argument is not a natural 
number but an *integer*. That means it can be negative. Given any integer, z, and any 
rotation, r, zpow returns rᶻ. If z is positive, this is z composed (\*) with itself n 
times.  If z is a negative number, -n, then the result is defined to be 1 / rᶻ (just
like in arithmetic). That in turn is just shorthand for (div 1 rᶻ).

So let's take care of inv and div first.  To instantiate these typeclasses for we first
need implementations for α = rot_syms


rotation-specific inv 
~~~~~~~~~~~~~~~~~~~~~~

TEXT. -/

-- QUOTE:
-- Here's our inverse operation
def rot_inv : rot_syms → rot_syms := _
-- it comes with ⁻¹ as a notation

-- Let's stick it in a has_inv instance for rot_syms
instance : has_inv rot_syms := _
-- QUOTE.

/- TEXT:

rotation-specific div
~~~~~~~~~~~~~~~~~~~~~

Instantiating has_div for rot_syms requires a 
rot_syms-specific implementation of div(ision).
This function just multiplies by the inv(erse).
TEXT. -/

-- QUOTE:
-- Here's our rotation-specific division operation
def rot_div (x y : rot_syms) :=  x * y⁻¹
-- note use of notations from monoid (*) and has_inv

-- Now wecan instantiate has_div for rot_syms 
instance has_div_rot_syms : has_div rot_syms := _
-- thus overloading div(ision) (/) for rot_syms
-- QUOTE.

/- TEXT: 

Demo
~~~~
TEXT. -/

-- QUOTE:
/-
Verify test correctness in your head by 
first expanding the definition of div, then
unfolding the application of ⁻¹, and finally
reasoning about the "geometry" of the example. 
-/
example :r240 / r240 = 1 := rfl

-- QUOTE.

/- TEXT:

div_inv_monoid
~~~~~~~~~~~~~~

Now we can turn to zpow. Its type is reported as ℤ → G → G, 
where, here, G = rot_syms. If the argument, (z :  ℤ), is not
negative, we know how to recurse down from z to 0 in order to
iterate some operation; but what do we do with argumentss that
are negative integers? More generally, how do we define a
function to compute a result for any values of type integer?  

The type definition is the key, as you'll have to define such
a function by cases analysis on constructor applications. The
key in turn is to understand how int terms are represented.   
TEXT. -/

-- QUOTE:
-- inductive definition of e int (with standard notation ℤ)
#check int
/-
inductive int : Type
| of_nat : nat → int
| neg_succ_of_nat : nat → int
-/
-- QUOTE. 


/- TEXT:
There are two forms of int value. Each incorporates a nat value (n). 
The term, (int.of_nat n), is the int representation of the injection of
the nat value, n, into the integers. So, for example, (int.of_nat 3) is
a term that represents the *integer,* not the natural number, 3. On the
other hand, The term, (int.neg_succ_of_nat n), represents the integer,
-(n+1). So, for example, (int.neg_succ_of_nat 0) represents -1, while
(int.neg_succ_of_nat 4) represents the integer value, -5. 

Admittedly the constructors seem strange at first, but they do provide 
one term for each and every integer. The +1 in the second assures that
we don't end up with two distinct representations of 0.

In any case, we now know how to write zpow for rot_syms: by case analysis 
on the incoming int argument as usual. The only remaining question is what
to do in each case. Note that zpow just generalizes npow to take negative
integer values as well non-negatives corresponding to natural numbers. Put
this together with the meaning of exponentiation by a negative value and
you're good to go!
TEXT. -/

-- QUOTE:
-- hint: think about rot_npow from monoid
def zpow_rot_syms : ℤ → rot_syms → rot_syms 
| (int.of_nat n) r := _           -- reminder: something about rot_npow, hmmm ...
| (int.neg_succ_of_nat n) r := _  -- reminder: rot_npow (and a negative exponent)

-- QUOTE.

/- TEXT:
TEXT. -/

-- QUOTE:

-- a little pain; use "show" to force rewrite of (a * b⁻¹)
theorem rot_inv_div : ∀ (a b : rot_syms), a / b = a * b⁻¹ :=
begin
end


/-
SEE Design note on div_inv_monoid/sub_neg_monoid and 
division_monoid/subtraction_monoid in the Lean source
file. Now let's build our group typeclass instance for
rot_syms.
-/ 

#check @div_inv_monoid.mk
/-
div_inv_monoid.mk :
  Π -- arguments
    {G : Type u_1} 
    (mul : G → G → G)
    (mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
    (one : G)
    (one_mul : ∀ (a : G), 1 * a = a) 
    (mul_one : ∀ (a : G), a * 1 = a) 
    (npow : ℕ → G → G)
    (npow_zero' : auto_param (∀ (x : G), npow 0 x = 1) (name.mk_string "try_refl_tac" name.anonymous))
    (npow_succ' : auto_param (∀ (n : ℕ) (x : G), npow n.succ x = x * npow n x) (name.mk_string "try_refl_tac" name.anonymous))
    (inv : G → G) 
    (div : G → G → G),  -- comma
    auto_param (∀ (a b : G), a / b = a * b⁻¹) (name.mk_string "try_refl_tac" name.anonymous) →
    Π (zpow : ℤ → G → G),
      auto_param (∀ (a : G), zpow 0 a = 1) (name.mk_string "try_refl_tac" name.anonymous) →
      auto_param (∀ (n : ℕ) (a : G), zpow (int.of_nat n.succ) a = a * zpow (int.of_nat n) a) (name.mk_string "try_refl_tac" name.anonymous) →
      auto_param (∀ (n : ℕ) (a : G), zpow -[1+ n] a = (zpow ↑(n.succ) a)⁻¹) (name.mk_string "try_refl_tac" name.anonymous) →
  div_inv_monoid G
-/

instance div_inv_monoid_rot_syms : div_inv_monoid rot_syms :=  
⟨
  rot_mul,
  rot_mul_assoc,
  1,
  rot_left_ident,
  rot_right_ident,
  rot_npow,
  _,                -- Lean infers these auto_param values
  _,
  rot_inv,
  rot_div,
  _,
  zpow_rot_syms,
  _,
  _,
  _
⟩ 

#eval @div_inv_monoid_rot_syms 

#check @group
#check @group.mk


-- QUOTE.
