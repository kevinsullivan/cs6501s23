
*****************************
Associating values with types
*****************************

If we take a step back, we can see that what we've done is to
associate certain values of the monoid type with given element
*types*. In particular, to the type, nat, we've associated two
monoid values: the additive monoid, ⟨ℕ, +, 0⟩ and separately 
the multiplicative monoid, ⟨ℕ, *, 1⟩; and to the type, list α,
we've associated the additive monoid value, ⟨list α, ++. []⟩.

In practice we often want to associate notations with the 
binary operations of monoid objects. We can for example, 
define *+* as a notation for *op* in an additive monoid, 
such as ⟨list,++,[]⟩, and *\** as a notation for *op* in a 
multiplicative monoid, such as ⟨nat, *, 1⟩. We can then use
the *+* and *\** notations to denote whathever operators
are recorded in the *op* field of any given monoid object.

For this to work (and for some other reasons) we'' define 
separate additive and multiplicative monoid types. In this
context, we will thus have a *one-to-one* mapping from nat
as an element type to each corresponding monoid type. That
is, there will be exactly one add_monoid structure for the
nat type, and one mul_monoid structure.  

- nat is associated with the (add_monoid nat), ⟨ℕ, +, 0⟩  
- list α is associated with the add_monoid, ⟨list α, ++, []⟩
- nat is associated with the (mul_monoid nat), ⟨ℕ, *, 1⟩

Sadly then, we'll also need two definitions of foldr, one that
takes any additive monoid as an argument and one that takes
a multiplicative monoid. The need to split definitions into
additive and multiplicative is counter-intuitive to most
mathematicians but is forced by our type theory. In practce,
Lean provides mechanisms for writing one definition and then
cloning it automatically to produce the code for the other.

.. code-block:: lean

  structure mul_monoid' (α : Type) : Type := mk::
    (op : α  → α  → α )   -- data
    (e : α )              -- data
    (ident : ∀ a, op e a = a ∧ op a e = a)
    (assoc: ∀ a b c, op a (op b c) = op (op a b) c)
  
  -- unfortunate but unavoidable duplication 
  structure add_monoid' (α : Type) : Type := mk::
    (op : α  → α  → α )   -- data
    (e : α )              -- data
    (ident : ∀ a, op e a = a ∧ op a e = a)
    (assoc: ∀ a b c, op a (op b c) = op (op a b) c)
  
  def  mul_foldr' {α : Type} (m : mul_monoid' α) : list α → α 
  | list.nil := match m with (mul_monoid'.mk op e _ _) := e end
  | (h::t) := match m with (mul_monoid'.mk op e _ _) := m.op h (mul_foldr' t) end
  
  def  add_foldr' {α : Type} (m : add_monoid' α) : list α → α 
  | list.nil := match m with (add_monoid'.mk op e _ _) := e end
  | (h::t) := match m with (add_monoid'.mk op e _ _) := m.op h (add_foldr' t) end


Foldr over any monoid
---------------------

Our next observation we make is that we can apply foldr to
a list of elements of some type α if and *only if* we have a
definition of a monoid for α. For example, given what we've
defined above, we can apply fold operation to lists of nat
and lists of list, but not to list of bool, because we have
not yet defined a monoid (additive or muliplicative) for the
bool type. 

In other words, to apply foldr to lists of elements of type,
α, we must *overload* the definition of *monoid* for the α 
type. What can *not* apply foldr to lists of elements of any
type, α, so we are *not* looking at *parametric polymorphism*
here. Rather, we're seeing a new concept: namely, *ad hoc* 
polymorphism. 

The list α type is *parametrically* polymorphic, in that it's 
defined in exactly the same way for *any* element type, α. By 
contrast, we have defined monoid α *instances* only for a few
selected types, namely nat and list α. We will further expect
to have only one instance of either add_monoid' or mul_monoid'
for any given type, α.  

Finally, given these constraints, we note an real opportunity. 
Consider an application of mul_foldr' to a list of natural 
numbers. From the fact that the list element type, α, is nat, 
we know is that mul_foldr' expects an instance of (mul_monoid' 
nat). Furthermore, there should be at most one instance of the 
(mul_monoid' nat) defined. Finally we have such an instance: 
nat_mul_monoid, as defined above will work. In other words, it
is the only monoid instance that we can use here. Wouldn't it 
be nice is Lean could infer that automatically and pass this
*value* implicitly to foldr? Note that this is a new idea: we
are not talking about *type* inference, but *value* inference.
