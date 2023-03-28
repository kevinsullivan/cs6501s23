
*******
Monoids
*******

This chapter has taught you about proof by induction. Our need
for this proof construction method was created by our need for  
proofs of some basic properties of all natural numbers: namely,
for any *a*, *0* is both a left and a right identity; and for any 
*a, b,* and *c,* that *a + b + c = (a + b) + c*. (As application
is left associative we omit explicit parentheses in *(b + c)*.)

The for these proofs in turn was driven by our need to specify
what it means to be a monoid, so that we could pass values of a 
*monoid* type to our favorite higher-order function, *foldr*,
rather than separate *operator* and *identity* arguments.

We now finish off this chapter by completing our task to specify
that it means in the abstract to be a *monoid* and how that will
enable us to define a version of *foldr* that wil works for any
monoid: extending its binary operator to an *n-ary* operator on
a list of argument values. 

We'll start with where we've gotten to up to now, and will then
take it the rest of the way from there. 

Where we've gotten to
---------------------

The concept of a *monoid* is a simple but important example of 
an algebraic structure. This chapter will explain how better to
formalize such structures in Lean, settings patterns for more 
abstract mathematics and for certain generalized programming
concepts as well. 

We defined a monoid type with one constructor (mk), polymorphic 
in the type element type, withan associative binary operator, 
*op*, and an identity element, *e*, for *op*.  

In this version the names *id* and *e* switched from our earlier
version. The letter *e* is often used to represent an identity
element, so we made that switch here.   

.. code-block:: lean

  
  structure monoid' {α : Type} : Type := mk::
    -- data values
    (op : α  → α  → α )   -- data
    (e : α )              -- data
    -- statements and proofs of laws
    (ident : ∀ a, op e a = a ∧ op a e = a)
    (assoc: ∀ a b c, op a (op b c) = op (op a b) c)

With a monoid type defined, we then defined several *instances,* 
one for each monoid of interest: ⟨nat, +, 0⟩,  ⟨nat, \*, 1⟩, and
*⟨list, ++, []⟩*. Here that is again using gour improved monoid
definition just above.  
Next we implemented a first version of foldr taking any monoid as an argument.
Here's a version improved only in presentation. The function type specification
clearly expresses what foldr does: given a monoid, m, it returns an n-nary operator
of type list α → α. Second, here for the first time we introduce Lean's match value
with <patterns> end construct. It lets you do case analysis via pattern matching on 
any value or multiple values anywhere an expression is expected in Lean. The syntax
is match _ with | case := return | case := return | ... end  (first is | optional)


.. code-block:: lean

  def foldr {α : Type} (m : @monoid' α) : list α → α  
  | list.nil := match m with (monoid'.mk op e _ _) := e end
  | (h::t) := match m with (monoid'.mk op e _ _) := m.op h (foldr t) end

Here are examples, first as we've seen previously, but then, using partial
evaluation to clearly show how foldr extends the binary operation of any 
monoid to an n-ary version taking its arguments from a list data structure.  

.. code-block:: lean

  -- Safe use of monoid instances folds
  #reduce foldr nat_add_monoid [1,2,3,4,5]
  #reduce foldr nat_mul_monoid [1,2,3,4,5]
  #reduce foldr monoid_list_append' [[1,2,3],[4,5,6],[7,8,9]]
  
  -- Defining n-ary operators(partial evaluation)
  def nat_add_n := foldr nat_add_monoid
  def nat_mul_n := foldr nat_mul_monoid
  def list_app_n {α : Type} := foldr (@monoid_list_append' α)  -- study this
  
  -- Applying n-ary versions of binary operators to *lists* of argument values
  #eval nat_add_n [1,2,3,4,5,6,7,8,9,10]
  #eval nat_mul_n [1,2,3,4,5,6,7,8,9,10]
  #eval list_app_n [[1,2,3],[4,5,6],[7,8,9]]
  #eval list_app_n [ ["Hello", ", ", "Logic!"], ["You", " ", "are", " ", "Cool!"]]

Exercise: Define monoid instances for Boolean && and Boolean ||
operators, and use them as arguments to foldr to define their 
n-ary extensions. 

Associating values with types
-----------------------------

Under construction.


Under Construction
------------------

In the last chapter we started on this project. This chapter will
finish it off with the introduction, explanation, and demonstration
of typeclasses as a mechanism for associating monoid values, such
as *⟨nat, +, 0⟩, ⟨nat, *, 1⟩,* and *⟨list, ++, []⟩*, with element 
types such as nat and list.  
