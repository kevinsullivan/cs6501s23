-- import .A_05_recursive_proofs

import algebra.group
namespace cs6501

/- TEXT: 

******
Review
******

Let's start by reviewing what we've done so far. 

Algebraic Structures
--------------------

The concept of a *monoid* is a simple but important example of 
an algebraic structure. An algebraic structure extends a set of
elements of some type with additional *structure*: here with a
binary operator and an identity element that follow the monoid
laws. 

The concept extends to all manner of algebraic structures. 
For example, a *group* is a monoid with the added structure
of an inverse operation, ⁻¹, such that every element, a, has
an inverse, a⁻¹, such that *op a a⁻¹ = op a⁻¹ = e. Note that
the additive monoid of natural numbers cannot be extended in
this way, but the additive monoid over the integers can be. 
Similarly, monoid extends semi-group, which in general has
an associative binary operator but no identity element. 

This chapter will explain how to formalize such structures 
in Lean, settings patterns for more abstract mathematics as
well as for important generalized programming abstractions,
as well. For example, we 'll see that *applicative functor*
objects extend function application to multiple arguments,
and that monads extend function composition to add useful
behaviors to it, in turn enabling apparently imperative 
styles of programming in pure functional languages.  

Monoids so far
--------------

We have so far defined one monoid type. It is a product
type, which is to say that it has just constructor (mk), 
with multiple argments, and can be thought of as defining
an ordinary *record* type. We associate such records with
element types, such as nat and list α, in order to extend
them with additional monoid structure. Such structure is
just what's needed for foldr to work properly, as we've
seen. 

Here's the definition of monoid we've developed so far. 
In this version we've swapped the names *id* and *e* from
last chapter (sorry), as the letter, *e,* is often used in
mathematical writing to denote an identity element.   
TEXT. -/ 

-- QUOTE:
structure monoid' (α : Type) : Type := mk::
  -- data values
  (op : α  → α  → α )   -- data
  (e : α )              -- data
  -- statements and proofs of laws
  (ident : ∀ a, op e a = a ∧ op a e = a)
  (assoc: ∀ a b c, op a (op b c) = op (op a b) c)
-- QUOTE.

/- TEXT:
With a monoid type defined, we then defined several *instances,* 
one for each monoid of interest: ⟨nat, +, 0⟩,  ⟨nat, \*, 1⟩, and
*⟨list, ++, []⟩*.   
TEXT. -/

-- QUOTE
-- monoid instances

def nat_add_monoid' := monoid'.mk nat.add 0 sorry sorry -- zero_ident_add_nat nat_add_assoc  
def nat_mul_monoid' := monoid'.mk nat.mul 1 sorry sorry -- mul_one_ident_nat nat_mul_assoc 
def monoid_list_append' {α : Type} : @monoid' (list α) := monoid'.mk list.append [] sorry sorry 


/- TEXT:
Next we implemented a first version of foldr taking any monoid as an argument.
Here's a version improved only in presentation. The function type specification
clearly expresses what foldr does: given a monoid, m, it returns an n-nary operator
of type list α → α. Second, here for the first time we introduce Lean's match value
with <patterns> end construct. It lets you do case analysis via pattern matching on 
any value or multiple values anywhere an expression is expected in Lean. The syntax
is match _ with | case := return | case := return | ... end  (first is | optional)

TEXT. -/

-- QUOTE:
def foldr' (α : Type) (m : monoid' α) : list α → α  
| list.nil := match m with (monoid'.mk op e _ _) := e end
| (h::t) := match m with (monoid'.mk op e _ _) := m.op h (foldr' t) end
-- QUOTE.

/- TEXT:
Here are examples using these constructs. .First we apply foldr to
a monoid α and a list α. Then, using partial evaluation, we apply
foldr just to the monoid argument, returning what amounts to an 
n-ary operation on lists of α values.   
TEXT. -/

-- QUOTE:
-- Safe use of monoid instances folds
#reduce foldr' nat nat_add_monoid' [1,2,3,4,5]
#reduce foldr' nat nat_mul_monoid' [1,2,3,4,5]
#reduce foldr' (list nat) monoid_list_append' [[1,2,3],[4,5,6],[7,8,9]]

-- Defining n-ary operators(partial evaluation)
def nat_add_n := foldr' nat nat_add_monoid'
def nat_mul_n := foldr' nat nat_mul_monoid'
def list_app_n {α : Type} := foldr' (list α)  (@monoid_list_append' α)  -- study this

-- Applying n-ary versions of binary operators to *lists* of argument values
#eval nat_add_n [1,2,3,4,5,6,7,8,9,10]
#eval nat_mul_n [1,2,3,4,5,6,7,8,9,10]
#eval list_app_n [[1,2,3],[4,5,6],[7,8,9]]
#eval list_app_n [ ["Hello", ", ", "Logic!"], ["You", " ", "are", " ", "Cool!"]]
-- QUOTE.

/- TEXT:
Exercise: Define monoid instances for Boolean && and Boolean ||
operators, and use them as arguments to foldr to define their 
n-ary extensions. 
TEXT. -/

