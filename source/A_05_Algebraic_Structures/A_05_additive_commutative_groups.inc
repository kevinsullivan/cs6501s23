
*******
Modules
*******

In the last chapter we met the notion of the
action of a group element on an object of another
type. We thus had an algebraic concept involving 
two types, which we called G and α, and where a
group action was instantiated as mul_action G α,
inheriting from has_mul M α, which provides the
(g • a) notation. The has_mul typeclass in turn 
requires only that M have a monoid structure. 

A *module* in abstract algebra similarly involves
two types: a semiring R and add_comm_monoid M.

additive commutative monoid
---------------------------

Class is add_comm_monoid.

Remember that an additive monoid is a set of objects
with an associative *addition* operation and an identity
element denoted as 0. Clearly the natural numbers with
nat.add and (0 : ℕ) forms a monoid. 

In an additive monoid, nsmul is the analog of npow in 
a multiplicative monoid. Whereas npow multiplies an
element, a, by itself n times, returning a^n, nsmul 
adds an element, a, to itself n times, returning n*a
(multiplication by a constant). The constraint that 
is added to an add_comm_monoid is that addition must
be commutative: the order in which you add doesn't 
matter: (∀ (a b : M), a + b = b + a).

.. code-block:: lean

  #check @add_comm_monoid.mk
  /-
  add_comm_monoid.mk : 
  Π {M : Type u} 
    (add : M → M → M) 
    (add_assoc : ∀ (a b c : M), a + b + c = a + (b + c)) 
    (zero : M) 
    (zero_add : ∀ (a : M), 0 + a = a) 
    (add_zero : ∀ (a : M), a + 0 = a) 
    (nsmul : ℕ → M → M), 
      auto_param 
          (∀ (x : M), nsmul 0 x = 0) 
          (name.mk_string "try_refl_tac" name.anonymous) → 
      auto_param 
          (∀ (n : ℕ) (x : M), nsmul n.succ x = x + nsmul n x) 
          (name.mk_string "try_refl_tac" name.anonymous) → 
    (∀ (a b : M), a + b = b + a) → 
  add_comm_monoid M
  -/


semi-ring
---------

"A semiring is a type with the following structures: 

- additive commutative monoid (add_comm_monoid)
- multiplicative monoid (monoid)
- distributive laws (distrib)
- and multiplication by zero law (mul_zero_class). 

The actual definition extends monoid_with_zero instead 
of monoid and mul_zero_class.
"

.. code-block:: lean

  #check @semiring 
  

multiplicative group, which is a group with a
multiplicative operator satisfying the group
axioms: the \* operator is associative; there
is an identity element, denoted 1; and every
element, g, has a multiplicative inverse, g^⁻¹. 

An additive group can similarly be understood
as a collection of actions, but the operator
on group elements is now +. Correspondingly, 
the identity is denoted 0, and the inverse of
any element, a, is denoted -a. The group rules
apply. For example, ∀ a, -a + a = 0 (group 0). 

It'll be worthwhile to have a simple example 
of an additive group. We will use the integers.
The associative operation will be +, the identity 
element is (0: int), and inverse is negation.  

Viewed as an action we will see a given integer, 
say 3, as operating on a target object by adding
itself to the target. The result of the action of
3 on a rational-valued target, 2.5, for example,
would be 3 + 2.5, where 3 is coerced from integer
to rational and the addition is rational number
addition. 

Interpreted geometrically, the target rations
represent points, and the actions of the integers
represent "translations." Such translations "add 
up" (because they're a group) by the axioms, we
know that applying a tranlation, (t₂ + t₁), for
any translations, t₁ and t₂, to an object, o, is 
the same as applying tranlation action t₂ to the 
result of applying translation action t₁ to o. 

Target Type
-----------

.. code-block:: lean

  inductive tri 

Typeclasses
-----------

To instantiate the mul_action typeclass, we'll have to
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


.. code-block:: lean

  /-
  @[ext, class]
  structure has_smul (M : Type u_1) (α : Type u_2) :
  Type (max u_1 u_2)
      smul : M → α → α
  -/


mul_action
~~~~~~~~~~


.. code-block:: lean

  /-
  universes u_10 u_11
  
  @[ext, class]
  structure mul_action (α : Type u_10) (α : Type u_11) [monoid α] :
  Type (max u_10 u_11) :=
  (    to_has_smul : has_smul α α)
  (    one_smul : ∀ (b : α), 1 • b = b)
  (    mul_smul : ∀ (x y : α) (b : α), (x * y) • b = x • y • b)
  -/


Instances
---------

has_smul rot tri
~~~~~~~~~~~~~~~~

.. code-block:: lean

  def mul_rot_tri : rot → tri → tri
  -- fill in
  
  
  instance : has_smul rot tri := _

mul_action rot tri
~~~~~~~~~~~~~~~~~~

.. code-block:: lean

  instance : mul_action rot tri :=
  sorry
  

Discussion
----------

