/- TEXT:

******************************
Simplified Propositional Logic
******************************


Our next step toward formalizing abstract mathematics for software 
engineering, we will specify the syntax and semantics of a simple 
but important mathematical language, namely *propositional logic*.

Propositional logic is isomorphic to (essentially the same thing 
as) Boolean algebra. You already know about Boolean algebra from 
writing conditions in if and loop commands in everyday programming 
languages such as Java.

Our first task will be to see how to formalize the syntax and 
semantics of this language in Lean. 

Syntax 
------

The set of expressions (strings) comprising the formal 
language of propositional logic is defined inductively. 
That is, some smallest expressions are first defined, 
with larger expressions then defined as being constructed, 
at least in part, from smaller ones *of the same type*.

The syntax of propositional logic comprises 

* variables, e.g., x, y, y, theSkyIsBlue, etc
* a language of propositional expressions (propositions)
  * constant expressions, *true* and *false*
  * variable expressions, such as X, Y, Z, TheSkyIsBlue, each such expression having an associated variable
  * operator expressions, such as ¬X, X ∧ Y, and X ∨ Y

You can think of these operators as taking expressions
as their arguments and returning longer expressions as 
their results.

To begin, we define a datatype the values of which will
represent our the variables. We'll name the type *prop_var,* 
for propositional variable. For now we'll assume we're 
restricted to using at most three variables.  We'll call
them *x, y,* and *z* and will just list them as being the
distinct constant values of the *prop_var* type.
TEXT. -/

-- QUOTE:
inductive prop_var : Type
| x
| y 
| z

open prop_var 
-- QUOTE.

/- TEXT:
Next we'll define the set of expressions in our language,
which we'll call *prop_expr*, the language of expressions
in propositional logic.
TEXT. -/

-- QUOTE:
inductive prop_expr
| var_expr (v : prop_var)
| and_expr (e1 e2 : prop_expr)
| or_expr (e1 e2 : prop_expr)

open prop_expr
-- QUOTE.

/- TEXT:
We can now form both variable and operator
expressions! Let's start with some variable
expressions.
TEXT. -/

-- QUOTE:
def X : prop_expr := var_expr x
def Y : prop_expr := var_expr y
def Z : prop_expr := var_expr z
-- QUOTE.

/- TEXT:
We can also define operator expressions, which
build larger expressions out of smaller ones.
TEXT. -/

-- QUOTE:
def XandY : prop_expr := and_expr X Y 
def XandY_and_Z : prop_expr := and_expr XandY Z 
-- QUOTE.

/- TEXT:

Semantics
---------

The semantics of propositional logic assigns a Boolean
truth value to each expression in the language, but to
do this, an additional piece of data is required: one
that defines the Boolean meaning (truth value) of each
*variable* referenced by any variable expression.

What for example is the meaning of the variable expression,
*X*? It's impossible to say unless you know the meaning of 
the variable, *x*. If the meaning of *x* is true, then we
define the meaning of *X* to be true, and likewise for the
value, false.

We will use the word *interpretation* to refer to any
assignment of Boolean truth values to all variables that
can be referenced by any given variable expression. For
example, we might define *x*, *y*, and *z* all to have
true as their meanings.  We can formalize this mapping
from variables to truth values as a total function from
terms of type *prop_var* to terms of type *bool* in Lean.

TEXT. -/  

-- QUOTE:
def all_true : prop_var → bool
| _ := tt   -- for any argument return true (tt in Lean)
-- QUOTE. 

/- TEXT:
Similarly here's an interpretation under which all variables
are assigned the value, false.
TEXT. -/

-- QUOTE:
def all_false : prop_var → bool
| _ := ff   -- for any argument return true (tt in Lean)
-- QUOTE. 

/- TEXT:
Now here's an interpretation under which x is assigned true, 
and the remaining variables (y and z) are assigned false.
TEXT. -/

-- QUOTE:
def mixed : prop_var → bool
| prop_var.x := tt
| _ := ff

#reduce mixed z

def another_interpretation : prop_var → bool
| x := tt
| y := ff
| z := tt
-- QUOTE. 

/- TEXT: 
Given one of these interpretations as additional data, we
can now assign truth value semantic meanings to expressions
such as XandY (and_expr X Y). We do this recursively. First
we evaluate X to get its truth value (by applying a given
interpretation function to the variable, x, that expression
X "contains". 

Recall that X is defined to be the term, var_expr x. We just
need to *destructure* this term to get the *x* part of it.
Remember that constructors simply package up their arguments
into terms in which those arguments appear in order. Once we
get at the variable, *x*, we just apply an interpretation 
function to it to get its corresponding Boolean value, and
we take that as the meaning of the variable expression, *X*. 

Ok, so what about the meaning of *(and_expr X Y)*? First we
need to know the meanings of *X* and *Y*. Suppose they are
true and false, respectively. Then we define the meaning of
*(and_expr X Y)* as the Boolean *conjunction* of these truth
values. In this case, that'd be *tt && ff,* which is *ff*.

Here then is a semantic evaluation function that implements
these two notions: one in the case where the expression to 
be given a meaning is a variable expression, and one where
it's an *and* expression.
TEXT. -/

-- QUOTE:
def prop_eval : prop_expr → (prop_var → bool) → bool 
| (var_expr v) i := i v
| (and_expr e1 e2) i := band (prop_eval e1 i) (prop_eval e2 i)
| (or_expr e1 e2) i := bor (prop_eval e1 i) (prop_eval e2 i)
-- QUOTE. 

/- TEXT:
Now we can find the meaning of *any* expression in our
initial subset of the language of propositional logic.
To be more precise, we'd say that we've specified an
*abstract syntax* for our language. In our next unit,
we'll see how to use Lean's syntax extension capabilities
to define a corresponding *concrete* syntax, one that'll
let us write expressions in our language as if we were
using paper and pencil methods and standard syntax for
propositional logic. 
TEXT. -/

-- QUOTE:

#check all_true 


#reduce prop_eval X all_true
#reduce prop_eval Y all_true
#reduce prop_eval Z all_true

#reduce prop_eval X all_false
#reduce prop_eval Y all_false
#reduce prop_eval Z all_false

#reduce prop_eval XandY all_true
#reduce prop_eval XandY all_false
#reduce prop_eval XandY mixed

#reduce prop_eval (and_expr (and_expr X Y) (or_expr X Z)) mixed
-- QUOTE.

/- TEXT:
So we now have is a specification of the syntax and 
semantics of a subset of propositional logic. As an 
in-class exercise, let's add some new logical operators:
for not, or, implies, bi-implication, and exclusive or. 
TEXT. -/

