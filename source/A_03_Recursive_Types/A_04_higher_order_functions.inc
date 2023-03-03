**********************
Higher-Order Functions
**********************

Higher-order functions are simply functions that consume
function definitions as arguments and/or return function
definitions as results. You've been seeing higher-order
functions from early in this class. 

Example: *pEval*
----------------

Consider our semantic evaluation function, *pEval,* for
propositional logic. It takes two arguments: an expression, *e*, 
and an *interpretation* *i,* in the form of a function from 
propositional variables to logical truth (Boolean) values. 

The type of *pEval* is thus *prop_expr → (prop_var → bool)
→ bool*. The second argument is a *function value*, which 
*pEval* uses to get the Boolean values of the *variables* 
in the expression to be evaluated. The fact that *pEval*
takes another function as an argument makes *pEval* a 
higher-order function.

More generally, whenever a function, *g*, takes a function,
*f* as an argument, then *g* is a higher-order function. 
You can think of *f* as a *little* machine (of a specific
type) that you hand to *g* and that *g* can then use to do
its job.

Exercise: Write a function, *apply_once,* polymorphic in 
types α and β, taking two arguments, a function value, 
f : α → β, and (2) an argument value, (a : α), that 
returns the value of type β obtained by applying f to a.

Exercise: Write a function, *apply_twice*, polymorphic
in a type, α, taking a function value, *f : α → α*, and
an argument value, *a : α*, and that returns the result
of applying f to the result of applying f to a. In other
words, return the result of applying f twice to a. 

Exercise: Write a function, *apply_n*, polymorphic in a
type, α, taking a function value, *f : α → α*, and an 
argument value, *a : α*, that returns the result gotten
by applying f to a n times. Observe that the type of this
higher-order function really gives you no choice as to 
what to return when n is zero. 

Exercise: Write a function, *apply_comp*, polymorphic 
in types, α, β, and γ, taking two functions, *f : α → β*, 
and *g : β → γ*, and an argument value, *a : α*, and that
returns the result obtained by applying g to the result 
obtained by applying f to a.  

Function composition
--------------------

Now just as a higher-order function can *use* other 
functions given as arguments, a higher-order function can
also *return* function values. Suppose, for example, that
you apply *apply_comp* to just two function values, without
giving the third argument. The result is a new function,
which we can write as (g ∘ f), pronouned as *g after f*, 
that takes an argument, *a*, and returns *g(f(a)).* 

As an exercise, let's write a version, *comp*, of 
*apply_comp* that leaves out the final argument. It will 
just take two functions of compatible types and return 
their composition.

.. code-block:: lean

  universe u
  def comp {α β γ : Type u} : (α → β) → (β → γ) → (α → γ)
  | f g := λ a, g ( f a)
  
  -- Standard notation reversing argument order: g after f
  
  notation : g ` ∘ ` f := comp f g
  

Exercise: Use comp to construct a new function, ev_len, 
that takes a string, s, and returns true (tt) if the length 
of s is even and false otherwise. 

You may use string.length to compute the length of a string
and (λ n, n % 2 = 0) to compute whether a given natural number
is even or not. 

You should explicitly declare the type of ev_len to be
string → bool.  Lean will then insert a coercion to convert 
the result of this check from a proposition (n % 2 = 0) to 
a bool value for you.  

.. code-block:: lean

  -- apply comp explicitly in your answer
  def ev_len : string → bool := _ 
  
  -- do it again but using ∘ notation
  def ev_len' := _
  
  -- test cases
  example : ev_len "Hello" = ff := rfl
  example : ev_len' "Hello" = ff := rfl
  example : ev_len "Hello!" = tt := rfl
  example : ev_len' "Hello!" = tt := rfl
  

Exercise: Write a function, comp_n, polymorphic in alpha that 
takes a function, f : α → α, and a natural number, n, and that
returns the function, f after f after f n times, i.e., the 
function obtained by composing f with itself n times. You'll 
see again that your hand is forced when deciding what to return
when n is zero. 

Higher-Order Functions on Lists
-------------------------------

map
~~~

The *map* function takes a list of values and transforms
it, element by element, into a new list of corresponding
values, obtained by applying the given function to each 
element in the given list. Note that the *map* function
never changes the *shape* of the list, only the *values*
that it holds. 

As specified below, we define *map* to be polymorphic in
the types of the elements in the given and returned lists,
respectively. It then takes a function that it will use to
convert values in the given list into corresponding values
for the new list.

Exercise: Given an English-language explanation of the
second pattern-matching rule below.

.. code-block:: lean

  universe v    -- u is already a universe level 
  
  def map {α : Type u} {β : Type v} : (α → β) → list α → list β 
  | f list.nil  := list.nil
  | f (h::t)    := (f h)::(map f t)
  
  -- nat → nat
  #eval map nat.succ [0,1,2,3,4]        
  #eval map (λ n, n * n) [0,1,2,3,4]
  
  -- string → nat
  #eval map string.length ["Hello", "Lean", "We", "Love", "You!"]
  
  #check @list.map
  

filter
~~~~~~

The filter function, polymorphic in a type, α, takes a list,
l, of α values and a *predicate function*, p, from α to bool, 
and returns the sublist of elements in l that *satisfy* p.


.. code-block:: lean

  -- In this example we also introduce "match" for doing case analysis on a term
  def filter' {α : Type u} : (α → bool) → list α → list α
  | p list.nil := list.nil
  | p (h::t) :=   
      match (p h) with 
        | tt := h::filter' p t
        | ff := filter' p t
      end
  
  #eval filter' ((λ n, n % 2 = 0) ∘ (string.length)) ["Hello", "Lean", "We", "Love", "You!"]
  
  -- same function using if/then/else; there's still a coercion happening from (p h) to bool 
  def filter {α : Type u} : (α → bool) → list α → list α
  | p list.nil := list.nil
  | p (h::t) := if (p h) then (h::filter p t) else (filter p t)
  


fold
~~~~

The *fold* function, also often called *reduce*, takes a list,
*l*, of values of some type, α, and reduces it to a single value 
of some type β. It is defined by case analysis on *l*. If *l* is
nil, fold needs to return an approriate result. For now, we will
pass this "value for the base case" as an additional argument to
fold. In the second, cases, where *l* is non-empty and thus of
the form, *h::t,* fold returns the result obtained by applying 
a given binary *reduction* function (also an argument) to (a) 
the head of the list, and (b) the *reduced* (folded) value of 
the rest of the list.

As an example, consider fold applied to the list [1,2,3] using
the binary operation, nat.add : nat → nat → nat as a reduction
operation. Here α = β = nat. The list is not nil, so we return
the result obtained by applying *nat.add* to 1 and the result
of reducing [2, 3] in the same way: fold nat.add [1,2,3] thus
reduces to *1 + fold nat.add [2, 3]*, which reduces to *1 + 2
+ fold nat.add [3]*, which reduces to *1 + 2 + 3 + fold nat.add
[]*. Clearly for this operation to return the right value, we
must define the last value to be zero. 

So how do we define this fold function precisely? It's by case
analysis on l. If l is nil, fold has to return the right value
for the given binary operation (zero in the preceding example). 
If l is not nil, then it's of the form (h::t), in which case the
fold function returns the result of applying the given reduction
operation to h and the result of recursively reducing the *rest*
of the list. 

- Give an English language explanation of how fold can be used to convert a list of strings into a bool, where the result is true (tt) iff the length of each string in the list is even. Pay close attention to the type of the reduction binary operation you will need to produce a working result.
- Exercise: Formalize the general type and give an implementation of the polymorphic fold function on lists.
- Exercise: Give a few examples of applications to bolster the case for the claim that it works correctly.
- Exercise: Use fold to implement a function that takes a list of strings and returns tt if all strings in the list are even length and false otherwise. Call it all_even. The trick will be to define the right reduction (binary) operation. Define it as a separate function, all_even_reducer.


.. code-block:: lean

  -- Your answer here:
  

Exercises
---------

- Write an analog of the map function not for lists but for option values. Call is map_option.
- Define a type, tree α, whose values are either empty or an α value and two smaller trees; then define a variant of the map function operating on such trees, calling it map_tree.
- There an interesting commonality here. How might one generalize our list-based map function to *any* type of data structure containing values of some type α, where what you want back is the same structure but with all the α values replaced by β values?
- Can you use parametric polymorphism to solve the preceding problem. Explain why or why not.

