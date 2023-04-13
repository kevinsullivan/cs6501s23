
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

We'll use the same method as in the last section to analyze
and then provide the values needed to instantiate the group
typeclass for a new type, with three values, representing the
set of symmetry rotations. We'll start top-down, with Lean's 
group typeclass, see what typeclasses it extends, and then
construct the elements needed to instantiate all of these
typeclasses, finally assembing all of these pieces into a
group typeclass instance for our set of rotation-representing
group elements. 








Typeclasses
-----------

In this section we'll go over the numerous typeclasses that
have to be instantiated before the group class can be. 

group
~~~~~

Here's the definition of the group typeclass in Lean. 


.. code-block:: lean

  #check @group
  /-
  class group (G : Type u) extends div_inv_monoid G :=
  (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
  -/

Every group is a monoid but with some additional structure,
namely inverses for every element. Inverses in turn enable
the definition division (multiplication by inverse) and the
definition of exponentiation of an element to integer powers,
including negatives.

[KS: Bothered by mismatch between hierarchy as taught in
school and the weirdly refactored abstractions we're seeing
here.]

monoid
~~~~~~

In Lean, the statement that every group is automatically 
a monoid means a few things. First, the group typeclass 
builds on (*extends*) monoid. Second, given  group typeclass
instance it will always be possible to extract from it a 
monoid instance. 

As something of a detailed design detail, In Lean, the
group class doesn't extend from monoid directly. Rather
it extends a typeclass call div_inv_monoid, representing
a monoid enriched with an inverse operation that behaves
like one, and a division operation defined simply as
(monoid) multiplication/composition by the inverse of
the second argument.

div_inv_monoid
~~~~~~~~~~~~~~

An instance of *div_inv_monoid α* provides 

- inv: binary operation, a⁻¹, from has_inv
- div: definition of a / b to be a * b⁻¹ 
- div_eq_mul_inv: proof of ∀ a b : G, a / b = a * b⁻¹ 
- left inverse: multiplying by inverse on left yields 1 *(∀ a, a⁻¹ * a = 1)*

, implements a⁻¹ inverse operation

We will now drill down on the div_inv_monoid typeclass. 

As a reminder, here it is again. We'll first look at the
classes it inherits, and then the field it adds to those
from its parent classes.  

.. code-block:: lean

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

This typeclass extends from the monoid, has_inv, and has_div classes
and then adds several additional fields. Let's first see what fields 
div_inv_monoid inherits from its parent classes.

From *monoid*, div_inv_monoid inherits the following: 

- mul, an associative binary operator, with notation (a * b) 
- e, an identity element for mul, with notation 1
- npow, for computing aⁿ by multiplication of a by itself n times
- npow_zero', a proof that a⁰ = 1
- npow_succ', a proof that npow n a is multiplication iterated n times (∀ (n : ℕ) x, npow n.succ x = x * npow n x . try_refl_tac))

From *has_inv*, div_inv_monoid inherits a single unary operator, 
inv (for inverse), for monoid elements, wotj the notation, a⁻¹. 
From the has_div class, div_inv_monoid obtains a single binary
operation, div, with notation (a / b) for (div a b).  So far, then, 
a div_inv_monoid instance will provide operators and notations for 
multiplication, exponentiation by a natural number, inverse, and 
division for monoid elements. 

The div_inv_monoid class then adds multiple fields values to
extend and constrain this inherited structure. Let's look at each 
of these fields in turn. 

- div, defining (a / b) as a * b⁻¹
- div_eq_mul_inv, requiring that division be multiplication by inverse
- zpow, which generalizes exponentiation to include negative exponents
- a proof of (∀ (x : rot), rot_npow 0 x = 1)
- a proof of (∀ (n : ℕ) (x : rot), rot_npow n.succ x = x * rot_npow n x)
- a proof of (∀ (a b : rot), a / b = a * b⁻¹)
- a proof of (∀ (n : ℕ) (a : rot), rot_zpow (int.of_nat n.succ) a = a * rot_zpow (int.of_nat n) a) :=
- a proof of (∀ (n : ℕ) (a : rot), rot_zpow -[1+ n] a = (rot_zpow ↑(n.succ) a)⁻¹)

Finally, to all of this structure the *group* typeclass adds one
additional constraint, (mul_left_inv : ∀ a : G, a⁻¹ * a = 1), which
requires that inv and mul work together correctly, in the sense that
for any monoid element, a, that mul (inv a) a = 1. We can say that
it requires a⁻¹ to always act as a *left inverse* for any *a*. 

To create a group typeclass instance, we need to instantiate the
parent typeclasses and then apply the group typeclass constructor
to the right arguments. We will now construct a group typeclass
instance for rot in a bottom-up manner, first constructing
instances for the parent typeclasses and finally instantiating
the group typeclass. 

To see what values have to be given to a typeclass constructor, 
you can #check the constructor type. So let's now do this for
the parent typeclasses, starting with has_inv and has_div, then
for div_inv_monoid, and finally for group. 

We'll tackle has_inv first. We check the constructor type to
see what arguments it needs. Then we construct the right
argument values: in this case an implementation of inverse
(inv) for rot in particular. And finally we instantiate
the typeclass. 

has_inv
~~~~~~~


.. code-block:: lean

  
  #check @has_inv
  #check @has_inv.mk 
  /-
  Π {α : Type u}, (α → α) → has_inv α
  
  The has_inv typeclass requires an implementation
  of a unary operation, inv, on α, and provides a⁻¹ 
  as a standard mathematical notation. It does not 
  constrain the behavior of inv in any way, leaving
  that task to downstream typeclasses that inherit
  from this one.  
  -/


Instances
---------

We'll build the required instances to enable construction
of a group typeclass instance for elements of type rot.

has_inv rot
~~~~~~~~~~~

To instantiate has_inv, we have to provide an implementation
of this operation for arguments of type rot. Once we have
that, the rest is straightforward. We'll call our overloaded
implementation function, rot_inv. We define the function by
case analysis on the rot argument, returning in each case
the rot value that when multiplied by the argument returns 
1. 

.. code-block:: lean

  open rot
  def rot_inv : rot → rot           -- HOMEWORK
  | r0 := r0
  | r120 := r240
  | r240 := r120
  
  instance : has_inv rot := ⟨ rot_inv ⟩  -- ⟨ ⟩ applies mk
  
  -- example, cool!
  #reduce r120^2

Instantiating has_inv gives us the ⁻¹ notation,
which we can use to assert that multiplying on
the left by the inverse always yields the identity.

.. code-block:: lean

  example : ∀ (r : rot), (r⁻¹ * r = 1) := 
  begin
  assume r,
  cases r,
  repeat {exact rfl, },
  end

Next we do the same thing for has_div: (1) define a binary
operation, rot_div, to use in overloading the generic div
function for values of type rot; then (2) instantiate 
the div typeclass using this value, which, among other things,
will provides (a / b) as a standard notation for a * b⁻¹
(which in turn of course desugars to mul a (inv b)).  

has_div rot
~~~~~~~~~~~

.. code-block:: lean

  def rot_div : rot → rot → rot := λ a b, a * b⁻¹ 
  instance : has_div rot := ⟨ rot_div ⟩  
  example : r240 / r240 = 1 := rfl


div_inv_monoid rot
~~~~~~~~~~~~~~~~~~

We now have typeclass instances for rot for each of the
typeclasses that div_inv_monoid extends. We now look at how
to instantiate div_inv_monoid for rot. We begin by looking
at the constructor for this typeclass. Here it is. 

.. code-block:: lean

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

From the constructor type we can see that we'll need to provide 
explicit argument values for mul, mul_assoc, one, one_mul, mul_one,
npow, npow_zero', and npow_succ', all which we already have from 
our instantiation of the monoid typeclass. We'll also need functions
for inv and div on rot elements, which we just produced. Finally
we'll need an implementation of zpow along proofs that it's behavior
satisfies certain axiom. 

Let's talk about zpow first. As you will recall, the npow function 
computes aⁿ (a multiplied by itself n times), where a is any monoid
element and n is any *natural number*, i.e., non-negative exponent 
value. The zpow function, by contrast, computes aᶻ, where z is any
integer value. If m is non-negative, then aᵐ is just (npow m a) but
returning an integer. If m is negative, we define aᵐ = 1 / a⁻ᵐ, as
in ordinary arithmetic. The division here is of course the monoid 
div function.   

We haven't previously defined a function with integer inputs, nor 
have we seen how the int type is defined in Lean. We will define
zpow by case analysis on its int argument, where the two cases
correspond to non-negative and negative values, respectively. To
prepare to define zpow, we need to understand the int type in more
details, so let's do that next, ending with a definition of zpow.

aside: int type
~~~~~~~~~~~~~~~

The integer type has two constructors. The first takes a natural
number, n, and returns it packaged up as an integer, int.of_nat n.
The second takes a natural number, n, and returns a term, namely
(int.neg_succ_of_nat n), representing -(n+1). 

.. code-block:: lean

  #check int
  /-
  inductive int : Type
  | of_nat : nat → int
  | neg_succ_of_nat : nat → int
  -/

Example will help. First, (int.of_nat 3) represents the *integer,* 
not the natural number, 3. Second, the term, (int.neg_succ_of_nat n), 
represents the integer, -(n+1), so (int.neg_succ_of_nat 0) represents 
-1, while (int.neg_succ_of_nat 4) represents the integer value, -5. 
Admittedly the constructors seem strange at first, but they do provide 
one term for each and every integer. The +1 in the second assures that
we don't end up with two distinct representations of 0.

In any case, we can now define zpow for rot by case analysis on
the *int* argument. The only remaining question is what to do in each 
case. 

.. code-block:: lean

  -- an example
  
  def isNeg : ℤ → bool 
  | (int.of_nat n) := ff
  | (int.neg_succ_of_nat n) := tt
  #eval isNeg (-5 : int)
  
  
  -- hint: think about rot_npow from monoid
  def rot_zpow : ℤ → rot → rot 
  | (int.of_nat n) r := rot_npow n r                    -- HOMEWORK 
  | (int.neg_succ_of_nat n) r := (rot_npow (n+1) r)⁻¹   -- HOMEWORK
  
  #reduce rot_zpow (-2:ℤ) r240 -- yay! expect 240
  
  

We now have all the building blocks needed to assemble
an instance of div_inv_monoid for objects of type rot. 
Here's the constructor type, again. Lean will infer values
of each field marked as auto_param, so when applying the
constructor, just use _ for each of these field values.  

.. code-block:: lean

  -- just to be explicit, we already have the following two proofs
  lemma rot_npow_zero : (∀ (x : rot), rot_npow 0 x = 1) :=
     monoid.npow_zero'
  
  lemma rot_npow_succ : (∀ (n : ℕ) (x : rot), rot_npow n.succ x = x * rot_npow n x) :=
    monoid.npow_succ'
  
  -- We need related proofs linking div and inv and proofs of axioms for zpow
  lemma rot_div_inv : (∀ (a b : rot), a / b = a * b⁻¹) :=
  begin
  assume a b,
  exact rfl,
  end
  
  lemma rot_zpow_non_neg : (∀ (n : ℕ) (a : rot), rot_zpow (int.of_nat n.succ) a = a * rot_zpow (int.of_nat n) a) :=
  begin
  assume n a,
  exact rfl,
  end
  
  def rot_zpow_neg : (∀ (n : ℕ) (a : rot), rot_zpow -[1+ n] a = (rot_zpow ↑(n.succ) a)⁻¹) :=
  begin
  assume n a,
  exact rfl,
  end
  
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
  
  #check rot_npow
  
  instance div_inv_monoid_rot : div_inv_monoid rot :=  
  ⟨
    rot_mul,
    rot_mul_assoc,
    1,
    rot_left_ident,
    rot_right_ident,
    rot_npow,
    rot_npow_zero,                -- autoparam
    rot_npow_succ,                -- autoparam
    rot_inv,
    rot_div,
    rot_div_inv,
    rot_zpow
  ⟩ 
  
  /-
  Now we can see the structure we've built!
  The proofs are erased in this presentation
  and only the computational data are named.
  -/
  #reduce @div_inv_monoid_rot 


group rot
~~~~~~~~~

And now, finally, we can instantiate the group class
for rot elements. 


.. code-block:: lean

  #check group 
  /-
  class group (G : Type u) extends div_inv_monoid G :=
  (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
  -/
  #check @group.mk
  /-
  Π {G : Type u_1} 
    (mul : G → G → G) 
    (mul_assoc : ∀ (a b c : G), 
    a * b * c = a * (b * c)) 
    (one : G)
    (one_mul : ∀ (a : G), 1 * a = a) 
    (mul_one : ∀ (a : G), a * 1 = a) 
    (npow : ℕ → G → G)
    (npow_zero' : auto_param (∀ (x : G), npow 0 x = 1) 
    (name.mk_string "try_refl_tac" name.anonymous))
    (npow_succ' :
      auto_param (∀ (n : ℕ) (x : G), npow n.succ x = x * npow n x) (name.mk_string "try_refl_tac" name.anonymous))
    (inv : G → G) (div : G → G → G)
    (div_eq_mul_inv : auto_param (∀ (a b : G), a / b = a * b⁻¹) (name.mk_string "try_refl_tac" name.anonymous))
    (zpow : ℤ → G → G)
    (zpow_zero' : auto_param (∀ (a : G), zpow 0 a = 1) (name.mk_string "try_refl_tac" name.anonymous))
    (zpow_succ' :
      auto_param (∀ (n : ℕ) (a : G), zpow (int.of_nat n.succ) a = a * zpow (int.of_nat n) a)
        (name.mk_string "try_refl_tac" name.anonymous))
    (zpow_neg' :
      auto_param (∀ (n : ℕ) (a : G), zpow -[1+ n] a = (zpow ↑(n.succ) a)⁻¹)
        (name.mk_string "try_refl_tac" name.anonymous)), (∀ (a : G), a⁻¹ * a = 1) → 
    group G
  -/
  
  lemma rot_left_inv:  (∀ (a : rot), a⁻¹ * a = 1) :=
  begin
  assume a,
  cases a,
  repeat {exact rfl},
  end
  
  
  instance : group rot := 
  ⟨
    rot_mul,
    rot_mul_assoc,
    1,
    rot_left_ident,
    rot_right_ident,
    rot_npow,
    rot_npow_zero,                -- autoparam
    rot_npow_succ,                -- autoparam
    rot_inv,
    rot_div,
    rot_div_inv,
    rot_zpow,
    rot_npow_zero,                -- same proof again
    rot_zpow_non_neg,             -- explicit typing needed
    rot_zpow_neg,                 -- same
    rot_left_inv
  ⟩ 
  

What we've finally done is to show that we can impose a
group structure on elements of type rot, given our
definitions of mul, inv, div, npow, and zpow. 

.. code-block:: lean

  #reduce r120 * r120               -- multiplication
  #reduce r120⁻¹                    -- inverses
  #reduce r120 / r240               -- division
  #reduce r120^4                    -- exponentiation by nat
  #reduce r120^(4:int)              -- exponentiation by non-negative int
  #reduce r120^(-4:int)             -- exponentiation by negative int
  

