/-
Under construction. Ignore. 

Rings
-----

As explained and stated in the mathlib documentation, a
semiring is a single type with these additionalstructures.  

- additive commutative monoid (add_comm_monoid)
  -- identity element for addition (zero, 0)
  -- associative addition operator (add, +)
  -- not npow but ... addition n times of a
  -- commutativity of +: ∀ a b, a + b = b + a 
- multiplicative monoid (monoid) 
  -- associative multiplication operator (mul, *)
  -- identity element for multiplication (one, 1)
  -- multiplication n times of a value (npow)
- distributive laws (distrib) 
  -- make addition and multiplication work together
  -- left_distrib: ∀ a b c, a * (b + c) = a * b + a * c
  -- right_distrib : ∀ a b c, (a + b) * c = a * c + b * c 
- multiplication by zero law (mul_zero_class)
  -- what is the axiom?

Without inverses, there is no division., but we do now 
have both (commutative) addition and (not necessarily
commutative) multipication of elements in a way that no
matter what those elements are obeys the distributive
laws, both left and right. So arithmetic with addition and
multiplication, identities, and n-times iterated addition
and multiplication. 

The actual definition extends monoid_with_zero instead 
of monoid and mul_zero_class separately.

https://leanprover-community.github.io/mathlib_docs/algebra/ring/defs.html#semiring
TEXT. -/

-- QUOTE:
/-
class semiring (α : Type u) extends 
  non_unital_semiring α, 
  non_assoc_semiring α, 
  monoid_with_zero α
-/
-- QUOTE. 

/- TEXT:

non_unital_semiring
^^^^^^^^^^^^^^^^^^^

non_assoc_semiring 
^^^^^^^^^^^^^^^^^^

monoid_with_zero
^^^^^^^^^^^^^^^^
  
additive commutative monoid
^^^^^^^^^^^^^^^^^^^^^^^^^^^

multiplicative monoid
~~~~~~~~~~~~~~~~~~~~~

distributive laws
~~~~~~~~~~~~~~~~~

multiplication by zero
~~~~~~~~~~~~~~~~~~~~~~

Modules
-------

Torsors over Modules
--------------------
TEXT. -/