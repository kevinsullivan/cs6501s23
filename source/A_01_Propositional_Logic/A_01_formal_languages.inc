
********************
Balanced Parentheses
********************

As a warmup, and to put some basic
concepts into play, we'll begin by specifying the syntax 
and semantics of a simple formal language: the language of
strings of balanced parentheses. Before we do that, we'll
better explain wht it all menas. So let's get started.

Formal languages
----------------

The syntax of a *formal language* defines a (possibly 
infinite) set of strings. Strings are sequences of symbols 
from some *alphabet* of symbols. The formal language of basic 
algebra, for example, includes strings such as *x*, *y*, and 
*x + y*, but not *x y*. Propositional logic includes *X*, *Y*, 
and *X ∧ Y* but not *X Y*. 

As another example, which shortly we will specify formally,
consider the language of all strings of balanced parentheses. 
The language includes the empty string, *(), (()), ((()))*, 
etc.  It does not include any unbalanced strings, such as 
*(*, *)*, *((*, or *(()*. 

Each string in our language will be of some finite nesting
depth (and thus length) but the number of strings in the 
language is infinite. There is one such string for each 
possible nesting depth of such a string. That is, for any 
natural number, *n*, there is a such a string with nesting
depth *n*. 

We clearly can't specify the set of strings by exhaustively
enumerating them expliciitly. There are too many for that. 
Rather, we need a concise, precise, finite, and manageable 
way to specify the set of all such strings. We will do that
by defining a small set of *basic rules for building* strings 
of this kind (we'll call them *constructors*), sufficient for 
constructing all and only the strings in the language.

We can specify the balanced parentheses language with just two
rules. First, the empty string, ∅, is in our language. Second, 
if *b* is *any* string in the language, then so is *(b)*. That
is all we need to construct a string of any nesting depth. 

The empty string (nesting depth 0) is just empty, while we can
construct a string of any positive depth by applying the first 
rule once, giving us the *base string*, ∅, any by applying the
second rule iteratively, first to ∅, as many times as needed to
construct a string of balanced parentheses as big as desired. 

A key characteristic of this definition is that it's properly
*inductive*. That is, it provides ways to build larger values
of a given type (balanced parenthesis strings) from smaller
values *of the same type*. The complete set of strings that
these rules *generate* (by any finite number of applications 
thereof) is exactly the set of strings, the *formal language*
that we set out to specify.

Paper & Pencil Syntax 
---------------------

What we've basically done in this case is to specify the set of
strings in our language with a *grammar* or *syntax definition*.
Such grammars are often expressed, especially in the programming
worls, using so-called *Backus-Naur Form (BNF)*. 

Backus first used BNF notation to define the syntax of the Algol 
60 programming language. BNF is basically a notation for specifying
what the linguist, Noam Chomsky, called *context-free grammars*. 

Here's a grammer in BNF for our language of balanced parentheses. 
We can say that the BNF grammar defines the syntax, or permitted
forms, of strings in our language. Be sure you see how this grammar
allow larger expressions to be build from smaller ones of the same 
kind (here *expression*).   

  expression ::= 
  | ∅ 
  | (expression)

This definition says that an expression (string) in our
language is either the empty string or it's an expression
within a pair of parentheses. That's it. That's all it takes.

Formal Syntax
-------------

Now we give an equivalent but *completely formal* definition
of this language in Lean. The key idea is that we will define
a new *data type* the values of which are all and only terms
representing strings in our language.

We'll start by defining separate data types (each with just 
one value) to represent left and right parentheses, respectively. 
The names of the types are *lparen* and *rparen.* Each has a 
single value that we will call *mk*. We can use qualified names
to distinguish these values: *lparen.mk* and *rparen.mk*. 

.. code-block:: lean

  inductive lparen 
  | mk
  
  inductive rparen
  | mk
  
  
  /- 
  Here are some examples where we use these values.
  In the first case we use *def* in Lean to bind a
  value (representing a left parenthesis) to the
  identifier, *a_lef_paren.* In the second case we
  used *example* in Lean as a way simply to exhibit
  a value of a particular type (here representing a
  right parenthesis).
  -/
  
  def a_left_paren : lparen := lparen.mk
  example          : rparen := rparen.mk

Now we're set to specify the set of all and only balanced
parenthesis strings. We give an inductive definition with
the two rules (*constructors*). First, the empty string 
(which for now we call mk_empty to stand for ∅), is in the
set of balanced strings. Second, if *b* is any balanced
string, then the term *mk_nonempty l b r* is also (that is
also represents) a balanced string, namely *(b)*.  

.. code-block:: lean

  inductive bal 
  | mk_empty
  | mk_nonempty (l: lparen) (b : bal) (r : rparen) 

The only thing that a constructor does in such a definition
is to package up its arguments (if any) into a new term with 
the constructor name as a first element (a label, if you will). 
The type system of Lean will now recognize any term that can
be built using the available constructors as being of type bal. 

Here we illustrate the use of these constructors to build the 
first few balanced strings in our language. We Open the *bal* 
namespace so that we don't have to write *bal.* before each 
constructor name. These constructor names do not conflict with 
any existing definitions in the current (global) namespace. 
We don't open the lparen and rparen namespaces because then 
we'd have two (ambiguous) definitions of the identifier, mk, 
and we'd have to write *lparen.mk* or *rparen.mk* in any case 
to disambiguate them. 

.. code-block:: lean

  open bal
  
  def b0 : bal :=       -- ∅ 
    mk_empty            
  
  def b1 : bal :=       -- (∅)
  mk_nonempty           -- constructor
    lparen.mk           -- argument left parenthesis
    b0                  -- note: we could write mk_empty
    rparen.mk           -- argument right parenthesis
  
  def b2 :=             -- ((∅))
  mk_nonempty  
    lparen.mk
    b1
    rparen.mk
  
  def b3 :=
  mk_nonempty
    lparen.mk
    (
      mk_nonempty
        lparen.mk
        (
          mk_nonempty
            lparen.mk
            mk_empty
            rparen.mk
        )
        rparen.mk
    )
    rparen.mk

You can confirm that the type of b1 is bal using the 
*check* command in Lean. The output of this  command is 
visible if you hover your cursor over the blue underline 
(in VSCode), and in your Lean infoview. You can open and
close the infoview window in VSCode by CMD/CTRL-SHIFT-ENTER. 

.. code-block:: lean

  #check b1

You can now use the *reduce* command in Lean to see that *b1* is 
bound to the term, *mk_nonempty lparen.mk mk_empty rparen.mk*. If
you do the same for *b2* you will see its unfolded value, and the
same goes for b3. Be sure to relate the results you get here back
to the definitions of *b1, b2,* and *b3* above.

.. code-block:: lean

  #reduce b1
  #reduce b2
  #reduce b3

From here we can build larger and larger strings in *bal*.

Inductive Datatype Definitions
------------------------------

There are three crucial properties of constructors of inductive
data types in Lean that you should now understand. First, they
are *disjoint*. Different constructors *never* produce the same
value. Second, they are *injective*. A constructor applied to
different argument values will always produce different terms.
Finally, they are complete. The langauge they define contains 
*all* of the strings constructible by any finite number of
applications of the defined constructors *and no other terms*. 
For example, our *bal* language doesn't contain any *error* or
any other terms not constructible by the given constructors. 

Semantics
---------

The semantics of a formal language defines an association 
between some or all of the terms of a language and what each
such term means, in some *semantic domain*. For example, we
can associate each string in *bal* with the natural number 
that describes its nesting depth. 

In this case, there is total function from terms of type 
*bal* to *ℕ*, so we can specify the semantics as a function
in Lean. (All functions in Lean represent total functions in
mathematics.)

Here is such a function defined using one of several notations
available in Lean. We define the function, *sem* as taking a
value of type *bal* as an argument and returning a value of
type nat (ℕ, natural number, i.e., non-negative integer) as
a result.

The function is defined by case analysis on the argument. If
it is the empty string, mk_empty, the function returns 0. 
Otherwise (the only remaining possibility) is that the value
to which *sem* is applied is of the form (mk_nonempty l b r)
where *l* and *r* are values representing left and right 
parenthesis, and where *b* is some smaller string/value of
type *bal*. In this case, the nesting depth of the argument
is one more than the nesting depth of *b*, which we compute
by applying *bal* recursively to *b*.


.. code-block:: lean

  def sem : bal → ℕ 
  | mk_empty := 0
  | (mk_nonempty l b r) := 1 + sem b
  
  -- We can now run some tests to see that it works
  #reduce sem b0
  #reduce sem b1
  #reduce sem b2

So there you have it. We've defined both a formal language 
and a semantics of this language using the logic of the Lean
proof assistant. We defined an inductive data type the *terms* 
(values) of which represent all and only the strings in *bal*.
We defined a total function that maps any term of this type to
its corresponding length expressed as a natural number, which
we take to be the *semantic meaning* of that string. 

We now have all the machinery we need to formally define the
syntax and semantics of more interesting and useful languages.
We will now turn to the language of propositional logic as our
next major example. 
