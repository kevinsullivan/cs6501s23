
***********
Typeclasses
***********

This chapter has taught you about proof by induction. Our need
for this proof construction method was created by our need for  
proofs of some basic properties of all natural numbers: namely,
for any *a*, *0* is both a left and a right identity; and for any 
*a, b,* and *c,* that *a + b + c = (a + b) + c*. (As application
is left associative we omit explicit parentheses in *(b + c)*.)

The need for these proofs in turn was driven by our need to specify
what it means to be a monoid, so that we could pass values of a 
*monoid* type, rather than separate *operator* and *identity* 
arguments, to our higher-order function, *foldr.

We now finish off this chapter by completing our task to specify
what it means, in the abstract, to be a *monoid*, how that will
enable us to define a version of *foldr* that wil works for any
monoid, and finally how the right monoid to use can be inferred
automatically from the type of elements in a given list. For that,
we will need the concept of typeclasses and typeclass inference.  

We'll start with where we've gotten to up to now, and will then
take it the rest of the way from there. 

Summary to Present
------------------

Let's start by reviewing what we've done so far. 

Algebraic Structures
~~~~~~~~~~~~~~~~~~~~

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
~~~~~~~~~~~~~~

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

.. code-block:: lean

  structure monoid' (α : Type) : Type := mk::
    -- data values
    (op : α  → α  → α )   -- data
    (e : α )              -- data
    -- statements and proofs of laws
    (ident : ∀ a, op e a = a ∧ op a e = a)
    (assoc: ∀ a b c, op a (op b c) = op (op a b) c)

With a monoid type defined, we then defined several *instances,* 
one for each monoid of interest: ⟨nat, +, 0⟩,  ⟨nat, \*, 1⟩, and
*⟨list, ++, []⟩*.   
Next we implemented a first version of foldr taking any monoid as an argument.
Here's a version improved only in presentation. The function type specification
clearly expresses what foldr does: given a monoid, m, it returns an n-nary operator
of type list α → α. Second, here for the first time we introduce Lean's match value
with <patterns> end construct. It lets you do case analysis via pattern matching on 
any value or multiple values anywhere an expression is expected in Lean. The syntax
is match _ with | case := return | case := return | ... end  (first is | optional)


.. code-block:: lean

  def foldr' (α : Type) (m : monoid' α) : list α → α  
  | list.nil := match m with (monoid'.mk op e _ _) := e end
  | (h::t) := match m with (monoid'.mk op e _ _) := m.op h (foldr' t) end

Here are examples using these constructs. .First we apply foldr to
a monoid α and a list α. Then, using partial evaluation, we apply
foldr just to the monoid argument, returning what amounts to an 
n-ary operation on lists of α values.   

.. code-block:: lean

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

Exercise: Define monoid instances for Boolean && and Boolean ||
operators, and use them as arguments to foldr to define their 
n-ary extensions. 

Associating values with types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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

Typeclasses
-----------

The typeclass mechanism of Lean, first implemented for Haskell,
provides exactly this capability. The basic idea is that if we
annotate the add_monoid' structure definition with *[class]* we
tell Lean to keep a table of monoid instance values, indexed by
the element type α, which it can then use later on to look up 
(infer) the monoid *instance* values that should be passed to
various applications of foldr.

Rather than declaring *structure mul_monoid'* we would declare 
*@[class] structure mul_monoid*, or just *class mul_monoid*.  

.. code-block:: lean

  @[class] structure mul_monoid (α : Type) : Type := mk::
    (op : α  → α  → α )   -- data
    (e : α )              -- data
    (ident : ∀ a, op e a = a ∧ op a e = a)
    (assoc: ∀ a b c, op a (op b c) = op (op a b) c)
  
  -- unfortunate but unavoidable duplication 
  class add_monoid (α : Type) : Type := mk::
    (op : α  → α  → α )   -- data
    (e : α )              -- data
    (ident : ∀ a, op e a = a ∧ op a e = a)
    (assoc: ∀ a b c, op a (op b c) = op (op a b) c)

Using the @[class] annotation tells Lean that we are defining
a structure whose instances are to be indexed by type values,
α. When we define an instance, we annotate it with @[instance]
or just use the *instance* keyword. 

.. code-block:: lean

  @[instance] def nat_add_monoid := add_monoid.mk nat.add 0 sorry sorry -- zero_ident_add_nat nat_add_assoc  
  instance nat_mul_monoid := mul_monoid.mk nat.mul 1 sorry sorry -- mul_one_ident_nat nat_mul_assoc 
  instance monoid_list_append {α : Type} : @add_monoid (list α) := add_monoid.mk list.append [] sorry sorry 


.. code-block:: lean

  def  mul_foldr {α : Type} [m : mul_monoid α] : list α → α 
  | list.nil := match m with (mul_monoid.mk op e _ _) := e end
  | (h::t) := match m with (mul_monoid.mk op e _ _) := m.op h (mul_foldr t) end
  
  def  add_foldr {α : Type} [m : add_monoid α] : list α → α 
  | list.nil := match m with (add_monoid.mk op e _ _) := e end
  | (h::t) := match m with (add_monoid.mk op e _ _) := m.op h (add_foldr t) end

Now we can apply foldr functions without having to give explict monoid 
instance arguments.

.. code-block:: lean

  
  #eval add_foldr [1,2,3,4,5]
  #eval add_foldr [[1,2,3],[4,5,6],[7,8,9]]
  #eval mul_foldr [1,2,3,4,5]

To finish this section, let's give another English reading
of the type specification of our foldr operations. We'll take 
mul_foldr as an example.

- def  mul_foldr {α : Type} [m : mul_monoid α] : list α → α 

We can now read this as follows: The mul_foldr operation takes
any element type, α, *as long as α has a multiplicative monoid
structure,* along with a list of α elements. It then returns a
value of the α type. In other words, the requirement that there
be a typeclass instance for α imposes a key *constraint* on the 
*type values* that can be passed to foldr. You can only apply
foldr to a list of values of type α if α has the structure of
a multiplicative monoid. 

Let's see what happens if we try to apply mul_foldr to a list
of values of a type, α, for which we have not yet defined a
monoid structure. As you will guess, Lean will tell us that
it can't infer a required typeclass instance. 

.. code-block:: lean

  #eval mul_foldr [tt,ff,tt]

In the next section, we'll see how typeclass "inheritance" can
be used to define rich and complex hierarchies of type classes.
For example, we'll define "group" as an extension of monoid with
an additional *inverse* operation and proof that every element
in a given group (e.g., of the integers or rationals) has an 
inverse. One could then pass any group to any function expecting
a monoid, because such an object "is" automatically a monoid too. 
