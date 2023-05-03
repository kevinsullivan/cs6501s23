
*******
Modules
*******

We've now undertood what it means to be a torsor over 
a group. A concrete example is our torsor of triangles 
over a group of rotational symmetries. That fact that
rotational symmetries form an additive group lets us 
do *additive group math* on symmetries: associative add, 
additively invert, subtract, zero left/right identity. 

In this chapter, we strengthen this concept by upgrading 
a mere additive group of actions/differences to a *module* 
of actions. In comparison with a group, G, a module adds a
set of scalars and an operation for multiplying group 
actions by scalars. 

For example, if s is a scalar and v is a group action,
then s • v is scalar multiplication of s and v yielding a
new, "scaled" group action. 

The set of scalars must form at least a *ring*, so you 
can add, invert, substract, and multiply scalars by each 
other (+, -, *). For example, the integers for a ring: 
you can multiply, add, invert, and thus subtract them,
but dividing them generally doesn't produce new integers.

If sclars have multiplicative inverses as well, and thus 
division, then you have a scalar *field*. For example, the
set of real numbers minus {0} forms a field. A module with
a scalar *field* is called a vector space.

The overall picture, then, is one in which, in a module, 
you can not only add, invert, and substract actions, but
you can also multiply (*scale*) them by scalars. Example:
if v₁ and v₂ are group actions and s₁ and s₂ are scalars,
then s₁ • (v1 +ᵥ v2) is also an action, s₁ • v₁ + s₁ • v₂; 
and (s₁ + s₂) • v1 = s• v₁ + s₁ • v₂, is too. A module is
a generalization of a vector space where you can't always 
compute inverses of scalars. 

Once we have modules, as richer sets of group actions, then
we'll be able to form torsors over *modules*. That takes us
right right up to the threshold of affine spaces, which are
simply torsors over *vector* spaces. Vector spaces are just
modules with that extra structure on their sets of scalars.

Modules in Lean
---------------

In Lean, one can form a module from an *additive commutative 
monoid* M, and a *semi-ring,* R, of scalars. A module relaxes
the need for an underlying *group* of actions by relaxing the
need for additive inverses of actions. And unlike a full ring, 
a semi-ring omits the requirement for additive inverses (and
thus subtraction) of scalars. 

Note that in a ring, the existence of additive inverses means
that 0 is a multiplicative zero (prove it to yourself); in a 
semi-ring, by contrast, without additive inverses, one has to
identify the multiplicative zero explicitly (and show that it
is one).

Example
-------

That all sounds pretty abstract. To make it more real, could
we turn our *group* of triangle rotations into a module? We
already have addition and subtraction of rotations. Would it
make sense to scale rotations? 

The answer is yes it does, but with restrictions. We can't 
scale rotations by real numbers, for example, as that would
give rise to fractional rotations (like 1/2 or r120) that 
would no longer be symmetries. We've already seen, however,
that it makes sense to multiply rotations by integers, as
that's nothing other than iterated addition. 

To turn our group of rotations into a module, we now have
most of what we need: ℤ will be our ring of scalars acting
to *scale* rotations, but only by integer amounts. If ℤ were
a field, we'd have a vector space, but it's not so we have a
module. 

Now if we have a rotation, m, from our *module* of rotations
and an integer, r, how should we define the scalar product,
r • m? The result needs to be another action, namely one that
is *scaled* by that integer value. As indicated above, what
will work is to define r • m as m added to itself r times.
And that is nothing other than the operation we already have
currently called rot_zpow : ℤ → rot → rot. 

Typeclasses
-----------

So that's the idea. Let's turn to analyze the typeclasses we
will have to instantiate to formally represent our module of
rotations. Then we'll have everything we need to have a torsor
of triangles over a module of rotations. 

module
~~~~~~

.. code-block:: lean

  /-
  -- here's the module typeclass
  class module (R : Type u) (M : Type v) [semiring R]
    [add_comm_monoid M] extends distrib_mul_action R M :=
  (add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
  (zero_smul : ∀x : M, (0 : R) • x = 0)
  
  -- and here's its constructor
  /-
  #check @module.mk
  /-
  module.mk :
    Π {R : Type u_1} 
      {M : Type u_2} 
      [_inst_1 : semiring R] 
      [_inst_2 : add_comm_monoid M]
      [_to_distrib_mul_action : distrib_mul_action R M],
      (∀ (r s : R) (x : M), (r + s) • x = r • x + s • x) → 
      (∀ (x : M), 0 • x = 0) → 
      module R M
  -/

Our aim is to define an instance, [module ℤ rot]. R = ℤ is the scalar type,
and it must have the structure of a semi-ring. Interestingly, M = rot need 
not be a full group, just a monoid, but its addition must be commutative.
Think about vector addition in linear algebra: it's commutative. That's how
we want elements of a module, or eventually a vector space, to behave. 

Why not does the Lean module typeclass require a semi-ring structure on R,
and not a ring structure? The long and short of it is that it's it's a mathlib 
design detail and all going to add up to the same stuff at the end, anyway, so
just go with it for now.
  
Next, to instantiate (module ℤ rot) we'll need a (distrib_mul_action ℤ rot)
instance. It will provide definitions of the scalar multiplication operation
and proofs of certain required properties.

Finally, we'll need to provide two new proofs, certifying that our definitions
satisfy the additional module axioms. The first requires scalar addition on the 
left to distribute over scalar multiplication in the usual way. The second then
requires that multiplying any rotation, x, by *scalar* 0 (r0 in our case) yields 
the zero *rotation*. The zero scalar zeros out any "vector." 

- add_smul: ∀ (r s : ℤ) (x : rot), (r + s) • x = r • x + s • x
- zero_smul: ∀ (x : rot), (0 : R) • x = 0

Now we can make sense of the module typeclass instance *constructor*.
You can see where each value below slots into the structure. The ℤ and 
rot type arguments will be implicit, along with the required typeclass 
instances We will then give the two new proof values explicitly.

We'll now address each required building block in turn:

- [semiring ℤ]
- [add_comm_monoid rot] 
- distrib_mul_action ℤ rot
- add_smul
- zero_smul

semiring ℤ 
~~~~~~~~~~

Quoting essentially verbatim from the mathlib documentation, a semiring is 
a type with the following structures: 

- additive commutative monoid (`add_comm_monoid`)
- multiplicative monoid (`monoid`)
- distributive laws (`distrib`)
- multiplication by zero law (`mul_zero_class`)

The actual definition extends `monoid_with_zero`instead of `monoid` and 
`mul_zero_class`. 

The semiring typeclass definition is quoted next. It's a bit arcane (again
largely for mathlib design purposes). 

.. code-block:: lean

  /-
  -- Here's the actual semiring typeclass definition and constructor. 
  
  @[protect_proj, ancestor non_unital_semiring non_assoc_semiring monoid_with_zero]
  class semiring (α : Type u) extends non_unital_semiring α, non_assoc_semiring α, monoid_with_zero α
  -/

Fortunately, Lean already has a semiring typeclass for ℤ, so we won't need to 
worry about instantiating that. Good news! We can skip the details of semiring
construction.  

add_comm_monoid ℤ rot
~~~~~~~~~~~~~~~~~~~~~

To see how to instantiate (add_comm_monoid rot) one can inspect the
typeclass definition and its constructor, mk. Rather than delving into
the "super-classes", we'll just see what's needed to use the constructor
and not worry about which super-classes provided which fields for now.  

.. code-block:: lean

  /-
  Here's the additive commutative monoid typeclass. It defines an additive monoid 
  with *commutative* `(+)`.
  
  @[protect_proj, ancestor add_monoid add_comm_semigroup]
  class add_comm_monoid (M : Type u) extends add_monoid M, add_comm_semigroup M
  -/
  
  #check @add_comm_monoid.mk
  /-
  Here's the constructor. We actually already have every field
  value from our prior work except for the proof of commutativity
  of (rot) addition required for the last field of this typeclass. 
  
  add_comm_monoid.mk : 
    Π {M : Type u} 
      (add : M → M → M) 
      (add_assoc : ∀ (a b c : M), a + b + c = a + (b + c)) 
      (zero : M) 
      (zero_add : ∀ (a : M), 0 + a = a) 
      (add_zero : ∀ (a : M), a + 0 = a) 
      (nsmul : ℕ → M → M), 
      auto_param (∀ (x : M), nsmul 0 x = 0) (name.mk_string "try_refl_tac" name.anonymous) → 
      auto_param (∀ (n : ℕ) (x : M), nsmul n.succ x = x + nsmul n x) (name.mk_string "try_refl_tac" name.anonymous) → 
      (∀ (a b : M), a + b = b + a) → 
    add_comm_monoid M
  -/


distrib_mul_action ℤ rot
~~~~~~~~~~~~~~~~~~~~~~~~

The (distrib_mul_action M A) typeclass extends mul_action M A typeclass
brings together a set of scalars, M, and a set of objects, A, on which
they act. We will have M = ℤ and A = rot, enabling scalar multiplication.
We'll dig down (up) to the mul_action superclass. We'll then have all
the information needed to instantiate (distrib_mul_action ℤ rot), giving
us well defined meanings for expressions such as (3:Z) • (r240 + r120).
Think of that as being like a scalar multiplication of a sum of vectors. 

.. code-block:: lean

  #check @distrib_mul_action
  /-
  @[ext] class distrib_mul_action (M A : Type*) [monoid M] [add_monoid A]
    extends mul_action M A :=
  (smul_zero : ∀ (a : M), a • (0 : A) = 0)
  (smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y)
  -/
  
  #check @mul_action
  /-
  class mul_action (α : Type*) (β : Type*) [monoid α] extends has_smul α β :=
  (one_smul : ∀ b : β, (1 : α) • b = b)
  (mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)
  -/


Typeclass instances
-------------------

Now we develop each missing operation and proof and 
instantiate each missing ℤ-rot specific typeclass 
instance so as to be able ultimately to construct 
a (module ℤ rot) instance. 

add_comm_monoid rot
~~~~~~~~~~~~~~~~~~~

We don't need to worry about typeclasses for ℤ as 
the ones we need are already provided by mathlib. 
So we'll turn to the next item on the list: to show 
rotations form an additive *commutative* monoid. For
that we are lacking only a proof of commutativity of
rotation addition.

.. code-block:: lean

  def rot_add_comm : ∀ (a b : rot), a + b = b + a :=
  begin
      assume a b,
      cases a,
      repeat {
        cases b,
        repeat {exact rfl},
      },
    end
  
  -- now we can have our typeclass instance for rot 
  instance : add_comm_monoid rot := 
  ⟨ 
    -- stuff we already have
    rot_add,
    rot_add_assoc,
    r0,
    rot_left_ident,
    rot_right_ident,
    rot_npow,         -- fix multiplicative-sounding name
    rot_npow_zero,
    rot_npow_succ,
    rot_add_comm,     -- the new proof here
  ⟩ 


distrib_mul_action ℤ rot
~~~~~~~~~~~~~~~~~~~~~~~~

First we'll define s • m to mean rot_zpow s m. 
In other workds, we'll define scalar multiplication 
integer s by rotation r to be: (1) for a non-negative
s, the rotation *added* to itself that many times 
(already implemented by rot_zpow), and for a negative
s by the additive inverse (negation) of that sum.
The  we'll need to prove that scaling a rotation b
by scalar (x * y) is the same as scalaing b first 
by y then by x. With that we can define an instance,
(mul_action ℤ rot). 
 

.. code-block:: lean

  instance : has_smul ℤ rot := ⟨ rot_zpow ⟩ 
  
  lemma rot_mul_smul : 
    ∀ (x y : ℤ) (b : rot), (x * y) • b = x • y • b := 
  begin
  sorry,
  end
  
  instance : mul_action ℤ rot :=
  ⟨
    -- one_smul
    begin
    assume b,
    cases b,
    repeat {exact rfl},
    end,
  
    -- mul_smul
    begin
    assume x y b,
    apply rot_mul_smul,       -- sorried
    end,
  ⟩

With our (mul_action ℤ rot) defined we now put together
the final peices needed for (distrib_mul_action ℤ rot). 
With this instance in hand, in the next subsection we 
instantiate (module ℤ rot), which was our aim: to have
not just a group, but a *module*, of rotation actions:
actions that we can add, subtract, and *scale* by values
from a *ring*. So let's get (distrib_mul_action ℤ rot)
constructed. 


.. code-block:: lean

  -- scaling the 0 rotation by any int leaves it as 0. 
  lemma rot_smul_zero : ∀ (a : ℤ), a • (0 : rot) = 0 := 
    begin
    simp [rot_zpow],
    end
  
  -- scalaing a sum of rotations is the sum of the scalaed rotations 
  lemma rot_smul_add : ∀ (a : ℤ) (x y : rot), a • (x + y) = a • x + a • y :=
    begin
    assume z x y,
    -- annoying: notation is blocking progress, use show to change notation 
    have fix : r0 = (0:rot) := begin exact rfl, end,
    -- by case analysis on x, y
    cases x,
    repeat {
      cases y,
      repeat {
        rw fix, 
        simp [rot_add],
      },
    },
    -- induction on z
    repeat {
    induction z with n negn,
    simp [rot_npow],
    simp [rot_zpow],
    },
    -- by commutativity of rot +
    apply rot_add_comm,
    apply rot_add_comm,
  end
  
  -- That's all we need for (distrib_mul_action ℤ rot)
  instance : distrib_mul_action ℤ rot :=
  ⟨
    rot_smul_zero,
    rot_smul_add,
  ⟩
  


semiring ℤ 
~~~~~~~~~~

As noted above we can rely on Lean to provide a
semi-ring structure for the integers. So we don't
have to do any more work on this issue. Here's a 
quick demo showing that Lean finds an instance on
its own. 

.. code-block:: lean

  def z_ring [ring ℤ] (r1 r2 : Z) := r1 * r2
  #reduce z_ring 3 4


module ℤ rot 
~~~~~~~~~~~~

And with that, we have everything we need to have the
structure of a ℤ-module of rotations (akin to a vector
space but much more general, as you can now see). It
makes sense to have integers as scalars for an additive
group of rotations, because it just amounts to iterated
addition, under which the group is closed. 

Note that using real numbers, ℝ, as scalars would break
our whole design. We have no way to represent half of a
symmetry rotation, for example: it wouldn't be one, as 
it'd leave a triangle rotated only halfway to the point
where it'd lay down perfectly on top of its original 
form.   

.. code-block:: lean

  -- Here it is. But we've left out a proof! TBD. Big TODO!
  instance : module ℤ rot :=
  ⟨ show ∀ (r s : ℤ) (x : rot), (r + s) • x = r • x + s • x,
    begin
    assume r s m,
    sorry,          -- oops
    end,
    begin
    assume x,
    exact rfl,
    end
  ⟩ 

Foolproof abstract mathematics
------------------------------

Now we can write foolproof abstract mathematics
involving a torsor of symmetric triangles and a
*module* of actions, where actions can be added,
subtracted, and scaled. 

.. code-block:: lean

  open tri
  #reduce ((3:ℤ) • r120) • t120
  #reduce ((-2:ℤ) • r120) • t120
  #reduce (((3:ℤ) - (2:ℤ)) • r120) • t120

