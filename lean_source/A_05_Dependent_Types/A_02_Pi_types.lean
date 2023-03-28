/- TEXT:

Introduction
------------

This chapter has explained the concept and the means of constructing proofs of
logical propositions (as well as values of computational types) of the form, 
*∀ (a : α), P a*, 

In the logical case, *P* is a predicate, P : α → Prop, *a* is a value of type 
*α*, and *P a* is thus a proposition that depends on *a*. A proof, *all_a_Pa*, 
of *∀ (a : α), P a,*  is thus a function that, applied to any *a : α,* returns 
a proof of *P a*.

What is notable is that the *type* of the return value depends on the *value* 
of the argument to the function. We've seen plenty of examples like this, even
from near the start of the course. What we have now is the conceptual framework
and language to give a name to what we're seeing here: dependent types. The
return type is a dependent type in that it depends on the value of the argument
to the function itself. 

We have not yet seen *computation* examples of dependent types but we soon 
will. As an example, we can define *∀ (n : nat), n_list n* to be a function
of *n* that returns a value of a type *n_list n*, of *n-length* lists of ℕ.
For example, if applied to the value, 3, this function could return [0,0,0],
or [1,2,3] but not [0,0], or [0,0,0,0].


Π Types
-------

A Pi type associates types with values. 
We define a predicate, Q, as an example 
to use in what follows. Q is true of any 
natural number *n* by the reflexivity of
equality.
TEXT. -/

-- QUOTE:
def Q (n : nat) := n = n
#check Q  -- "propositions are types"
-- QUOTE.

/- TEXT:
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
TEXT. -/

-- QUOTE: 
-- Q n is a type (proposition) dependent on n
#check Q 0
#check Q 1
#check Q 2
-- QUOTE.

/- TEXT:

Dependent Function Types
~~~~~~~~~~~~~~~~~~~~~~~~

The next insight to gain is that we can now define
functions that return *values of dependent types*. 
To continue the preceding example, we define a new
function that when given *n* returns not the type,
n = n, but a proof of it: a value of the dependent
type. 
TEXT. -/

-- QUOTE:
-- A function from n : ℕ to *proofs (values)* of *Q n*
def dep_func_prop (n : ℕ) : Q n := begin unfold Q end
-- QUOTE.


-- QUOTE:
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
-- QUOTE.