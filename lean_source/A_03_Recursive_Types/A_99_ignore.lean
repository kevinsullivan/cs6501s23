import data.vector

namespace hidden
-- QUOTE:
universe u
def id { α : Sort u } (a : α) := a
/-
The *type* of the second argument, *a*, depends on 
the *value* of the first parameter, *α*.
-/

inductive list (α : Type u) 
| nil : list
| cons (h : α) (t : list) : list

#check @list.cons
/-
The constructors are polymorphic implicitly in α. We can
see this in the type of *list.cons : Π {α : Type u_1}, α → 
list α → list α*. For any type, *α*, the *cons* constructor
builds a new list from a value, *h* (for head), of type *α*, 
and from *t,* (for tail), a smaller *list α* value, returning
the term, *(cons h t)*, representing the list in which *h* is
prepended to *t* (written *h::t*). The salient point here is
that the *type* of the final return value of *cons, list α,* 
depends on the *value* of *α*. 
-/

def ev (n : ℕ) : Prop := n % 2 = 0 

#check (ev 0)
#check (ev 1)
#check (ev 2)
/-
These object are propositions, and propositions are types
that inhabit the universe, Prop.
-/

#check @vector

inductive nlist (α : Type u) (len : ℕ) 
| nil : nlist
| cons (h : α)

-- QUOTE.
end hidden


#check list







/- TITLE:
Introduction
------------

A predicate, as we've seen, is a function from objects to propositions
*about* them. For example, the predicate, *is_even := λ n, n % 2 = 0* 
is a function that takes a natural number, *n*, and yields a proposition
*about n*, namely that that particular value, *n*, modulo *2*, is equal
to zero: *n % 2 = 0*.
TEXT. -/

-- QUOTE:
-- a predicate, of type ℕ → Prop, yielding propositions "about" n
def is_even (n : ℕ) : Prop := n % 2 = 0
-- QUOTE.

/- TEXT:
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