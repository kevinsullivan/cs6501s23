**********************
Higher-Order Functions
**********************

A higher-order function is simply a function that
takes functions as arguments and/or that returns a 
function as a result.

In Logic
--------

We've already seen this idea in logical reasoning,
where function values are proofs of implications.
In this chapter, we'll see that same idea in the
realm of computation.

Let's start by reviewing a logical example to 
refresh memories. We'll review the proof that
*implication is transitive*: if the truth of some
proposition, P, implies the truth of Q, and if the
truth of Q implies the truth of R, then the truth 
of P implies that of R. Thinking computationally,
if we have a function, pq, that converts any proof 
of P into a proof of Q (a proof of P → Q), and a 
function, qr, that converts any proof of Q into a 
proof of R (a proof of Q → R), then we can build
a function, pr, that converts any proof, p, of P, 
into a proof of R (the desired proof of P → R) by 
applying the proof of P → Q to p to get a proof of
Q, and by then applying the proof of Q → R to that 
value to get a proof of R. Here it is formally. 

.. code-block:: lean

  example {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) := 
  begin
  assume pq qr,   -- assume P → Q and Q → R
  assume p,       -- to show P → R, assume p a proof of P
  exact qr (pq p) -- and derive the desired proof of R
  end

This proof is a higher-order function, albeit in the
realm of logic not computation with ordinary data. It 
takes two function arguments (one proving of P → Q and
the second proving Q → R) and returns a function that,
by converting any proof of P into a proof of R, proves
P → R. Therefore, (P → Q) → (Q → R) → (P → R). That is,
*implication is transitive*. 

Composition
-----------

What do we get when we construct the same argument not 
for proofs of logical propositions but for functions on
ordinary data? What we get is a higher-order function
that performs *function composition*. Note the change 
from Prop (logic) to Type (computation) in the following
definition. 

.. code-block:: lean

  example {α β γ : Type} : (α → β) → (β → γ) → (α → γ) :=
  begin
  assume αβ βγ,   -- assume f g
  assume a : α,   -- assume a
  exact βγ (αβ a) -- return λ a, g (f a)
  end

Compare and contrast this definition with the statement 
and proof of the transitivity of implication. See that
you've already been using higher-order functions albeit
to reason with functions that serve as proofs of logical
implications, rather than with with functions on ordinary
data. 

Let's write this definition a little more naturally,
and give it a name: *comp*, short for  *composition*.

.. code-block:: lean

  def comp {α β γ : Type} (f : α → β) (g : β → γ) : α → γ :=
  fun (a : α), g (f a)


Example
~~~~~~~

Let's see an example. Suppose we have two functions, *inc*
that increments a natural number and sqr that squares one.
We can form a function that first increments then squares
its argument by *composing* these two functions.

.. code-block:: lean

  def inc (n : ℕ) := n + 1
  def sqr (n : ℕ) := n * n
  def inc_then_sqr := comp inc sqr
  example : inc_then_sqr 5 = 36 := rfl   -- seems to work!


Notation
~~~~~~~~

Lean defines the infix operator ∘ as notation for function
composition. Note that the order of the function arguments
is reversed. (g ∘ f) is the function that applies g after
applying f to its argument. That is, (g ∘ f) x = g (f x).
We pronounce the function, (g ∘ f), as *g after f.*

.. code-block:: lean

  def inc_then_sqr' := sqr ∘ inc        -- composition!
  example : inc_then_sqr' 5 = 36 := rfl -- seems to work!


Example With Two Types
~~~~~~~~~~~~~~~~~~~~~~

In this example, given functions that compute the length
of a list and decrement a natural number, we construct a
function that takes a list of objects and returns one less
than its length. We first illustrate applications of Lean
functions for length and decrement and then use both our
notation and the Lean ∘ notation to construct the desired
function, which we apply to the list [1,2,3] yielding the
value, 2. 

.. code-block:: lean

  #eval list.length [1,2,3] -- apply length function to list
  #eval [1,2,3].length      -- function application notation
  #eval nat.pred 3          -- apply decrement function to 3
  
  -- Apply composition of length and pred to list
  #eval (comp list.length nat.pred) [1,2,3] 
  #eval (nat.pred ∘ list.length) [1,2,3]

The infix notation is best. Think of the argument, here the
list [1,2,3], as moving left through list.length, yielding 3, 
which then moves left through nat.pred, finally yielding 2.

Map
---

In this section, we introduce the *map* function on lists.
It takes (1) a function that takes objects of some type
α and converts them into objects of some type β, and (2) a
list of objects of type α, and returns a list of objects 
of type β, obtained by using the function to turn each each 
α object in the given list into a corresponding β object 
in the resulting list. 

We build to a general definition of map starting with a 
special case: of a function that takes a list of natural
numbers and returns a list in which each is increased by
one, by the application of *inc*, our increment function.

We define a function that "maps" the increment function
over a given list of natural numbers by case analysis on
any given list. If the given list is nil, we return nil;
otherwise, if the list is (h::t) we return the list with
the value of (inc h) at its head and the list obtained
by similarly incrementing each value in the tail of the
given list as its tail. 

.. code-block:: lean

  
  def inc_list_nat : list nat → list nat 
  | list.nil := list.nil  
  | (h::t) := (inc h)::inc_list_nat t
  
  -- it works
  #eval inc_list_nat[]        -- expect []
  #eval inc_list_nat [1,2,3]  -- expect [2,3,4]

Suppose that instead of incrementing each element 
of a given list to obtain a new list, we want to
square each element. One way to do it is to clone
the function above and replace inc with sqr.

.. code-block:: lean

  def sqr_list_nat : list nat → list nat 
  | list.nil := list.nil 
  | (h::t) := (sqr h)::sqr_list_nat t
  
  -- It works
  #eval sqr_list_nat [1,2,3,4,5]

Clearly we can clone and edit the preceding code
to produce a version that applies *any* function of
type nat → nat, instead of inc or sqr, to the head
of the given list, with all of the remaining code
unchanged, to map given lists of natural numbers 
to new lists by replacement of existing elements
with new elements computed by application of the
given function. 

That all the code remains the same but for the 
*element* converting function suggests that we
can instead *generalize* by making this function
a *parameter* of the otherwise unchanging code. 

.. code-block:: lean

  def any_list_nat : (nat → nat) → list nat → list nat 
  | f list.nil := list.nil 
  | f (h::t) := f h::any_list_nat f t
  
  -- It seems to work!
  example : any_list_nat sqr [1,2,3,4,5] = [1,4,9,16,25] := rfl    
  example : any_list_nat inc [1,2,3,4,5] = [2,3,4,5,6] := rfl
  example : any_list_nat nat.pred [1,2,3,4,5] = [0,1,2,3,4] := rfl

We've generalized the nat → nat function, but suppose we wanted
to convert a list of *strings* to a list of their natural number
lengths. We don't have the machinery to do that yet, as we can
only map functions over lists of natural numbers. Otherwise we
get a type error.

.. code-block:: lean

  #eval any_list_nat string.length ["I", "Love", "Math"]  -- nope!

One solution is simply to write a new version of our mapping
function specialized to map lists of strings to lists of nat
values, using any given string → nat function to perform the
element-wise mapping.

.. code-block:: lean

  def xyz_list_nat : (string → nat) → list string → list nat 
  | f list.nil := list.nil 
  | f (h::t) := f h::xyz_list_nat f t
  
  -- It seems to work
  #eval xyz_list_nat string.length ["I", "Love", "Math"]
  
  /-
  But we run into the same problem as before if we now want
  to map lists of strings to Boolean values, e.g., reflecting
  whether the length of each string is even (tt) or not (ff).
  Cloning code and editing it to produce another special case
  is really not the best solution.
  -/
  def map_string_bool : (string → bool) → list string → list bool 
  | f list.nil := list.nil 
  | f (h::t) := f h::map_string_bool f t
  
  -- is_even takes a nat and return tt if it's even else ff
  --
  def is_even (n : nat) : bool := n % 2 = 0
  #eval is_even 2
  #eval is_even 3
  
  /-
  Now we can map a function that tells whether a given string
  is of even length or not over any given list of strings to 
  get a corresponding list of tt/ff values.
  -/
  def is_even_length := is_even ∘ string.length
  #eval map_string_bool is_even_length ["I", "Love", "Math"]

Of course well run into exactly the same sort of problem,
of having to engage in error-prone cloning and editing of
code, if we want to now map lists of Boolean values to lists 
of strings (e.g., mapping each tt to "T" and each ff to "F"). 

And you can imagine many other examples: mapping lists of
employees to list of their corresponding salaries, or mapping
lists of Boolean values to lists of their negations, etc. The
possibilities are endless. 

The answer should now we pretty clear: we need to further 
generalize: not only over the function to apply to map each
list element, but also over the the types of element in the
input and output lists! Here, then, is a greatly generalized
version. 

.. code-block:: lean

  def map_list {α β : Type} : (α → β) → list α → list β 
  | f list.nil := list.nil
  | f (h::t) := f h :: map_list f t
  
  -- It seems to work!
  #eval map_list nat.succ [1,2,3]
  #eval map_list is_even_length ["I", "Love", "Math"]

For now, we'll be satisfied with this level of generality.
We will just observe that our mapping function still only
works for *lists* as element containers. What if you wanted
to map functions over other kinds of element "containers,"
e.g., to turn values of type *option α* into *option βs*?
Or trees of α values into corresponding trees of β values?

The key roadblock will be that there's no way to do this
using exactly the same code for, say, lists and options.
So the kind of parametric polymorphism we've been using
will no longer be enough. The answer will be found in a
different kind of polymorphism, *ad hoc* polynorphism, of 
which *operator overloading* (as in C++) is an example. 
For instance, you can write complex number and string
classes and overload the + operator in each class to do
respective complex number addition and string append, but
the implementations of these operations will hardly share
the same code. Completely different implementations will
be needed, to be selected (by the compler in C++) based
on the types of the arguments to which the + operator is
applied.  More on this topic later.

Fold
----

We now turn to a very different higher-order function
appliable to lists. It's called *fold* (or event better, 
*fold_right*) or *reduce*. 

The fundamental purpose of this operation is to turn a 
*binary* operation on the values of any given type (e.g., 
nat) into an operation that can be applied to *any* number
of arguments, where the arguments are packaged into a list
data structure.

The way the generalized version of the binary operation
works is that for the empty list it returns a base value,
and for a non-empty list, *h::t*, it applies the binary
operation to *h* and *to the result of applying the n-ary
version to the rest of the list, *t*. 

As an example, fold will turn the addition function on 
natural numbers (nat.add) into an operation that can be
applied to a list of any number of natural number values
to compute the sum of them all. Here, for example, is 
such a program. 

.. code-block:: lean

  def reduce_sum : list nat → nat
  | list.nil := 0
  | (h::t) := nat.add h (reduce_sum t)
  
  #eval reduce_sum []           -- sum of zero arguments
  #eval reduce_sum [5]          -- sum of one argument
  #eval reduce_sum [5,4]        -- sum of two arguments
  #eval reduce_sum [5,4,3,2,1]  -- sum of five arguments

It should be clear that we will want to generalize
the binary operator from nat.add to *any* binary
operation on natural numbers. For example, we might
want a function that implements n-ary multiplication,
reducing any list of natural numbers to the product
of all the numbers in the list. 

This is a little bit tricker than one might guess. 
To see the problem, let's clone and edit the code 
we've got, substituting multiplication for addition,
in an attempt to implement n-ary multiplication.  

.. code-block:: lean

  def reduce_prod' : list nat → nat
  | list.nil := 0
  | (h::t) := nat.mul h (reduce_prod' t)
  
  #eval reduce_prod' [3,2,1]   -- expect 6 got 0!
  
  /- 
  To see what goes wrong, let's unroll the recursion:
  - reduce_prod' [3,2,1] =
  - mul 3 (reduce_prod' [2,1]) =
  - mul 3 (mul 2 (reduce_prod' [1])) =
  - mul 3 (mul 2 (mul 1 (reduce_prod' []))) =
  - mul 3 (mul 2 (mul 1 0)) = 0!
  The problem is now clear, and so is the solution:
  we need to return a different value for the base
  case of an empty list when the binary operation is
  multiplication rather than addition. Specifically,
  we need to return 1 rather than zero. You can now
  probably guess that in general we want to return
  the *identity, or neutral, value* for whatever
  the binary operator is for the base case. Here
  we want to return 1.
  -/
  
  def reduce_prod : list nat → nat
  | list.nil := 1
  | (h::t) := nat.mul h (reduce_prod t)
  
  #eval reduce_prod []          -- expect 1
  #eval reduce_prod [5,4,3,2,1] -- expect 120

So now we can correctly generalize fold_nat over
binary operators by making the operator a parameter
but by also adding as a second parameter the right
identity element for whatever operator we provide
as an actual parameter.

.. code-block:: lean

  def fold_nat (op : nat → nat → nat):  nat → list nat → nat
  | id list.nil := id  
  | id (h::t) := op h (fold_nat id t)
  
  
  -- It seems to work!
  #eval fold_nat nat.add 0 [1,2,3,4,5]  -- expect 15
  #eval fold_nat nat.mul 1 [1,2,3,4,5]  -- expect 120

Yet a problem remains. There is nothing in our
solution that prevents us from passing the wrong
value for the identity element for the given binary
operator. The following function application runs
without any errors being reported but it gives the 
wrong answer, because we pass the wrong identity 
element for nat.mul. 

.. code-block:: lean

  #eval fold_nat nat.mul 0 [1,2,3]  -- oops, wrong

We will finish this chapter with a step toward our
ultimate solution: we will now construct a version
of fold_nat (fold_nat') that *enforces consistency*
between the binary function and identity element
arguments by requiring, as an additional argument,
a proof that the putative identity element really
is one! 

.. code-block:: lean

  def fold_nat' 
    (op: nat → nat → nat) 
    (id :nat) 
    (right_id : ∀ (n : nat), op n id = n) : 
    list nat → nat
  | list.nil := id  
  | (h::t) := op h (fold_nat' t)

Let's construct named proofs that 0 is an identity
when it appears as the second argument to nat.add.

.. code-block:: lean

  theorem zero_right_id_add : ∀ (n : nat), nat.add n 0 = n :=
  begin
  assume n,
  simp [nat.add]
  end 
  
  -- Now we can safely use fold_nat' 
  #eval fold_nat' nat.add 0 zero_right_id_add [1,2,3]
  
  -- This application fails because the proof is wrong
  #eval fold_nat' nat.add 1 zero_right_id_add [1,2,3]

As a closing point, we circle back to the notion that
fold generalizes any given binary operator to an n-ary
operator applicable to any number of arguments as long
as they're arranged in a list. You can see this idea 
in action by just partially applying fold_nat' to a
binary operator, it's identity, and the required proof,
leaving the list argument TBD.

.. code-block:: lean

  
  def n_ary_add := fold_nat' nat.add 0 zero_right_id_add
  
  -- It seems to work!
  #eval n_ary_add []            -- zero arguments
  #eval n_ary_add [5]           -- one argument
  #eval n_ary_add [4,5]         -- two arguments
  #eval n_ary_add [1,2,3,4,5]   -- five arguments, etc!

Soon we'll be able similarly to turn binary multiplication
into n-ary multiplication, with a definitions like this:
*def n_ary_mul := fold_nat' nat.mul 1 one_right_id_mul*. The
problem is we don't yet have the machinery (namely proof by
induction) to construct the proof that 1 is a right identity
for nat.mul. That'll come soon enough. For now, we can stub
it out and get something that works but without a proof that
1 is a right identity for natural number multiplication.

.. code-block:: lean

  def n_ary_mul := fold_nat' nat.mul 1 sorry
  #eval n_ary_mul [1,2,3,4,5]

Summary
-------

Higher-order functions are functions that consume functions
as arguments and/or that return functions as results. In this
chapter we've produced highly general higher-order functions
for (1) composition of functions, (2) mapping functions over
lists to derive new lists, and (3) extending binary operators
to n-ary operators whose arguments are given as lists of any
length. 

Exercises
---------

1. Write a function, n_ary_append (without using fold) that 
takes a list of lists of objects of some type, α (the type will
be *list (list α)*) and that reduces it to a single list of α 
using *list.append* as a binary operation. For example, it'd
turn this list, [[1,2],[3,4],[5]] into the list [1,2,3,4,5].
You may use Lean's list.append function as a binary operator
that combines two lists into one. 

2. Write a function (without using fold) that takes a a list 
of lists of α and that returns the sum of the lengths of the
contained lists. For example applying your function to the
list, [[],[1,2,3],[1,2,3,4,5]], should return 8: the sum of
0 for the first list, 3 for the second, and 5 for the third. 
Your function will work by adding the length of the head of
the list of lists to the result of recursively reducing the
*rest* (tail) of the list of lists. You may use list.length
to compute the length of any list.

3. Write a function without using fold that takes a list of
lists of α and that returns true if the length of each of 
the elements lists is even and false otherwise.  
