
.. code-block:: lean

  -- a predicate, of type ℕ → Prop, yielding propositions "about" n
  def is_even (n : ℕ) : Prop := n % 2 = 0

What's interesting from the perspective that propositions are types is
that each distinct value of *n* gives rise to a different proposition:
one about 0, another about 1, a third about 2, and so on. These types
in turn just vary in terms of what specific value of *n* then mention. 
A predicate is thus a function that (in general) takes some arguments
and returns a type/proposition *that depends on those values*. Applying
the predicate *is_even* to *3,* for example, yields the *proposition,* 
*3 % 2 = 0*. This type expresses a particular claim *about 3.* 

More generally, in Lean we can define functions that take arguments of
some *index* type and that return *types* that depend on those values.
TITLE.
-/