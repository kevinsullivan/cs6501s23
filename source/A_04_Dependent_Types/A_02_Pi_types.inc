
Π Types
-------

A Pi type associates types with values. 
We define a predicate, Q, as an example 
to use in what follows. Q is true of any 
natural number *n* by the reflexivity of
equality.

.. code-block:: lean

  def Q (n : nat) := n = n
  #check Q  -- "propositions are types"

Indexed Families 
~~~~~~~~~~~~~~~~

Note that each *n* to to which one applies 
*Q* gives rised to a proposition--a type--that 
*is about* (and in this sense, depends on) *n*. 
Such a types is said to be a *dependent type*.

Parametric polymorphism, by contrast, arises
when *types* are parameters. For example, the 
*list* type builder takes an *type* (of list
elements)  as an argument and reduces to the 
type of lists of elements of that type. On the 
other hand, here the result type depends on a 
data *value*.

In effect, *Q* associates a separate type with
each nat value. We say that *Q* defines a family
of types *indexed by n*.  

.. code-block:: lean

  -- Q n is a type (proposition) dependent on n
  #check Q 0
  #check Q 1
  #check Q 2


Dependent Function Types
~~~~~~~~~~~~~~~~~~~~~~~~

The next insight to gain is that we can now define
functions that return *values of dependent types*. 
To continue the preceding example, we define a new
function that when given *n* returns not the type,
n = n, but a proof of it: a value of the dependent
type. 

.. code-block:: lean

  -- A function from n : ℕ to *proofs (values)* of *Q n*
  def dep_func_prop (n : ℕ) : Q n := begin unfold Q end


.. code-block:: lean

  #check dep_func_prop
  
  #check dep_func_prop 0
  #check dep_func_prop 1
  #check dep_func_prop 2
  
  #reduce dep_func_prop 0
  #reduce dep_func_prop 1
  #reduce dep_func_prop 2
  
  variables 
    (α : Type)          -- a *data* type
    (P : α → Prop)      -- predicate on α   
  
  #check ∀ (a : α), P a
  #check Π (a : α), P a

