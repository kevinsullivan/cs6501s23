-- BOTH:
import topology.metric_space.basic

/- TEXT:
.. _proving_facts_about_algebraic_structures:

Proving Facts about Algebraic Structures
----------------------------------------

.. index:: order relation, partial order

In :numref:`proving_identities_in_algebraic_structures`,
we saw that many common identities governing the real numbers hold
in more general classes of algebraic structures,
such as commutative rings.
We can use any axioms we want to describe an algebraic structure,
not just equations.
For example, a *partial order* consists of a set with a
binary relation that is reflexive and transitive,
like ``≤`` on the real numbers.
Lean knows about partial orders:
TEXT. -/
section
-- QUOTE:
variables {α : Type*} [partial_order α]
variables x y z : α

-- EXAMPLES:
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- QUOTE.

/- TEXT:
Here we are adopting the mathlib convention of using
letters like ``α``, ``β``, and ``γ``
(entered as ``\a``, ``\b``, and ``\g``)
for arbitrary types.
The library often uses letters like ``R`` and ``G``
for the carries of algebraic structures like rings and groups,
respectively,
but in general Greek letters are used for types,
especially when there is little or no structure
associated with them.

Associated to any partial order, ``≤``,
there is also a *strict partial order*, ``<``,
which acts somewhat like ``<`` on the real numbers.
Saying that ``x`` is less than ``y`` in this order
is equivalent to saying that it is less-than-or-equal to ``y``
and not equal to ``y``.
TEXT. -/
-- QUOTE:
#check x < y
#check (lt_irrefl x : ¬ x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
lt_iff_le_and_ne
-- QUOTE.

end

/- TEXT:
In this example, the symbol ``∧`` stands for "and,"
the symbol ``¬`` stands for "not," and
``x ≠ y`` abbreviates ``¬ (x = y)``.
In :numref:`Chapter %s <logic>`, you will learn how to use
these logical connectives to *prove* that ``<``
has the properties indicated.

.. index:: lattice

A *lattice* is a structure that extends a partial
order with operations ``⊓`` and ``⊔`` that are
analogous to ``inf`` and ``max`` on the real numbers:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variables {α : Type*} [lattice α]
variables x y z : α

-- EXAMPLES:
#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right: y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
-- QUOTE.

/- TEXT:
The characterizations of ``⊓`` and ``⊔`` justify calling them
the *greatest lower bound* and *least upper bound*, respectively.
You can type them in VS code using ``\glb`` and ``\lub``.
The symbols are also often called then *infimum* and
the *supremum*,
and mathlib refers to them as ``inf`` and ``sup`` in
theorem names.
To further complicate matters,
they are also often called *meet* and *join*.
Therefore, if you work with lattices,
you have to keep the following dictionary in infd:

* ``⊓`` is the *greatest lower bound*, *infimum*, or *meet*.

* ``⊔`` is the *least upper bound*, *supremum*, or *join*.

Some instances of lattices include:

* ``inf`` and ``max`` on any total order, such as the integers or real numbers with ``≤``

* ``∩`` and ``∪`` on the collection of subsets of some domain, with the ordering ``⊆``

* ``∧`` and ``∨`` on boolean truth values, with ordering ``x ≤ y`` if either ``x`` is false or ``y`` is true

* ``gcd`` and ``lcm`` on the natural numbers (or positive natural numbers), with the divisibility ordering, ``∣``

* the collection of linear subspaces of a vector space,
  where the greatest lower bound is given by the intersection,
  the least upper bound is given by the sum of the two spaces,
  and the ordering is inclusion

* the collection of topologies on a set (or, in Lean, a type),
  where the greatest lower bound of two topologies consists of
  the topology that is generated by their union,
  the least upper bound is their intersection,
  and the ordering is reverse inclusion

You can check that, as with ``inf`` / ``max`` and ``gcd`` / ``lcm``,
you can prove the commutativity and associativity of the infimum and supremum
using only their characterizing axioms,
together with ``le_refl`` and ``le_trans``.
TEXT. -/
-- QUOTE:
example : x ⊓ y = y ⊓ x := sorry
example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := sorry
example : x ⊔ y = y ⊔ x := sorry
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := sorry
-- QUOTE.

-- SOLUTIONS:
example : x ⊓ y = y ⊓ x :=
begin
  apply le_antisymm,
  repeat {
    apply le_inf,
    { apply inf_le_right },
    apply inf_le_left }
end

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) :=
begin
  apply le_antisymm,
  { apply le_inf,
    { apply le_trans,
      apply inf_le_left,
      apply inf_le_left },
    apply le_inf,
    { apply le_trans,
      apply inf_le_left,
      apply inf_le_right },
    apply inf_le_right  },
  apply le_inf,
  { apply le_inf,
    { apply inf_le_left },
    apply le_trans,
    apply inf_le_right,
    apply inf_le_left },
  apply le_trans,
  apply inf_le_right,
  apply inf_le_right
end

example : x ⊔ y = y ⊔ x :=
begin
  apply le_antisymm,
  repeat {
    apply sup_le,
    { apply le_sup_right },
    apply le_sup_left }
end

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) :=
begin
  apply le_antisymm,
  { apply sup_le,
    { apply sup_le,
      apply le_sup_left,
      { apply le_trans,
        apply @le_sup_left _ _ y z,
        apply le_sup_right } },
    apply le_trans,
    apply @le_sup_right _ _ y z,
    apply le_sup_right },
  apply sup_le,
  { apply le_trans,
    apply @le_sup_left _ _ x y,
    apply le_sup_left },
  apply sup_le,
  { apply le_trans,
    apply @le_sup_right _ _ x y,
    apply le_sup_left },
  apply le_sup_right
end

/- TEXT:
You can find these theorems in the mathlib as ``inf_comm``, ``inf_assoc``,
``sup_comm``, and ``sup_assoc``, respectively.

Another good exercise is to prove the *absorption laws*
using only those axioms:
TEXT. -/
-- QUOTE:
theorem absorb1 : x ⊓ (x ⊔ y) = x := sorry
theorem absorb2 : x ⊔ (x ⊓ y) = x := sorry
-- QUOTE.

-- SOLUTIONS:
theorem absorb1αα : x ⊓ (x ⊔ y) = x :=
begin
  apply le_antisymm,
  { apply inf_le_left },
  apply le_inf,
  { apply le_refl },
  apply le_sup_left
end

theorem absorb2αα : x ⊔ (x ⊓ y) = x :=
begin
  apply le_antisymm,
  { apply sup_le,
    { apply le_refl },
    apply inf_le_left },
  apply le_sup_left
end

-- BOTH:
end

/- TEXT:
These can be found in mathlib with the names ``inf_sup_self`` and ``sup_inf_self``.

A lattice that satisfies the additional identities
``x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)`` and
``x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)``
is called a *distributive lattice*. Lean knows about these too:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variables {α : Type*} [distrib_lattice α]
variables x y z : α

#check (inf_sup_left : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
#check (inf_sup_right : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z))
#check (sup_inf_left : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
-- QUOTE.

end

/- TEXT:
The left and right versions are easily shown to be
equivalent, given the commutativity of ``⊓`` and ``⊔``.
It is a good exercise to show that not every lattice
is distributive
by providing an explicit description of a
nondistributive lattice with finitely many elements.
It is also a good exercise to show that in any lattice,
either distributivity law implies the other:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variables {α : Type*} [lattice α]
variables a b c : α

-- EXAMPLES:
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) :=
sorry

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
  a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) :=
sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) :=
by rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h,
    ←sup_assoc, @inf_comm _ _ c a, absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
  a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) :=
by rw [h, @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b), h,
    ←inf_assoc, @sup_comm _ _ c a, absorb1, sup_comm]

-- BOTH:
end

/- TEXT:
It is possible to combine axiomatic structures into larger ones.
For example, an *ordered ring* consists of a commutative ring together
with a partial order on the carrier
satisfying additional axioms that say that the ring operations
are compatible with the order:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variables {R : Type*} [ordered_ring R]
variables a b c : R

-- EXAMPLES:
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
-- QUOTE.

/- TEXT:
:numref:`Chapter %s <logic>` will provide the means to derive the following from ``mul_pos``
and the definition of ``<``:
TEXT. -/
-- QUOTE:
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
-- QUOTE.

/- TEXT:
It is then an extended exercise to show that many common facts
used to reason about arithmetic and the ordering on the real
numbers hold generically for any ordered ring.
Here are a couple of examples you can try,
using only properties of rings, partial orders, and the facts
enumerated in the last two examples:
TEXT. -/
-- QUOTE:
example : a ≤ b → 0 ≤ b - a := sorry

example : 0 ≤ b - a → a ≤ b := sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := sorry
-- QUOTE.

-- SOLUTIONS:
theorem aux1 : a ≤ b → 0 ≤ b - a :=
begin
  intro h,
  rw [←sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b],
  apply add_le_add_left h
end

theorem aux2 : 0 ≤ b - a → a ≤ b :=
begin
  intro h,
  rw [←add_zero a, ←sub_add_cancel b a, add_comm (b - a)],
  apply add_le_add_left h
end

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c :=
begin
  have h1 : 0 ≤ (b - a) * c,
  { exact mul_nonneg (aux1 _ _ h) h' },
  rw sub_mul at h1,
  exact aux2 _ _ h1
end

-- BOTH:
end

/- TEXT:
.. index:: metric space

Finally, here is one last example.
A *metric space* consists of a set equipped with a notion of
distance, ``dist x y``,
mapping any pair of elements to a real number.
The distance function is assumed to satisfy the following axioms:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variables {X : Type*} [metric_space X]
variables x y z : X

-- EXAMPLES:
#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
-- QUOTE.

/- TEXT:
Having mastered this section,
you can show that it follows from these axioms that distances are
always nonnegative:
TEXT. -/
-- QUOTE:
example (x y : X) : 0 ≤ dist x y := sorry
-- QUOTE.

-- SOLUTIONS:
example (x y : X) : 0 ≤ dist x y :=
begin
  have : 0 ≤ dist x y + dist y x,
  { rw [←dist_self x],
    apply dist_triangle },
  linarith [dist_comm x y]
end

-- BOTH:
end

/- TEXT:
We recommend making use of the theorem ``nonneg_of_mul_nonneg_left``.
As you may have guessed, this theorem is called ``dist_nonneg`` in mathlib.
TEXT. -/