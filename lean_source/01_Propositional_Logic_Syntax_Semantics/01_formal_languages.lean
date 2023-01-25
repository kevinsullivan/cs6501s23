/- TEXT:

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
The language includes the empty string, *(), (()), ((())), etc. 
It does not include any unbalanced strings, such as *(*, *)*, 
or *(()*. 

The number of strings in this language is infinite, one for 
each possible finite nesting depth of such a string. That is,
for any natural number, n, there is a string with that nesting
depth. 

We clearly can't specify the set of strings by exhaustively
enumerating them. There are too many for that. Rather, we need 
a concise and precise way to specify rules for buildng all and
only the strings in the language.

We can specify the balanced parentheses language with just two
rules. First, the empty string, let's write it as ∅, is a string 
in our language. Second, if *b* is *any* string in the language, 
then so is *(b)*. 

We can construct a string of any nesting depth in this language
by applying the first rule once then the second rule as many
(finite) times as needed to construct the desired string. The
length of each such string is finite but the number of strings 
in the language is infinite. 

Syntax
------

We can write this set of rules somewhat more formally as
a *grammar* expressed in so-called *Backus-Naur Form*, or
BNF, as follows: 

  expression ::= 
  | ∅ 
  | (expression)

This definition says that an expression (string) in our
language is either the empty string or it's an expression
within a pair of parentheses. That's it. 

You can see that the strings *generated* by this grammar 
include the empty string, and any longer string of balanced 
parentheses. It isn't possible with these rules to produce 
a string with unbalanced parentheses. So we have a grammar
for the language we've described informally up to now. 

Next we give an equivalent and *completely formal* definition
of this language in Lean.  We'll start by defining separate 
data  types, each with just one value, to represent left and 
right parentheses, respectively. The names of the type are 
*lparen* and *rparen* and each has a single value (in the 
form of a constructor that takes no arguments and is thus a
constant) that we will call *mk*. 
TEXT. -/

-- QUOTE:
inductive lparen 
| mk

inductive rparen
| mk


-- named and anonymous demo/test values
def a_left_paren : lparen := lparen.mk
example          : rparen := rparen.mk
-- QUOTE.

/- TEXT:
Next we specify the set of balanced parenthesis strings.
It's an inductive definition. First, the empty string, ∅, 
is balanced. We represent it as the term mk_empty of type
bal. The second *constructor*, *mk_nonempty* takes three
arguments: (1) any term, l, of type lparen, (2) any balanced
string, b, (3) any term, r, of type rparen. It then packages 
these arguments into the term, *mk_nonempty l b r*. 
TEXT. -/

-- QUOTE:
inductive bal 
| mk_empty
| mk_nonempty (l: lparen) (b : bal) (r : rparen) 
-- QUOTE.

/- TEXT:
The only thing that a constructor does in such a definition
is to package up its arguments (if any) into a new term with 
the constructor name as a label. The type system of Lean will 
now recognize any such term as also being of type bal. Here 
are definitions of the first few balanced strings in our new
language. 

WE Open the bal namespace so that we don't have to write 
*bal.* before each constructor name of *bal*. These names
do not conflict with any existing definitions in the current
(global) namespace. We don't open the lparen and rparen
namespaces because then we'd have two (ambiguous) definitions
of the identifier, mk, and we'd have to write *lparen.mk* or
*rparen.mk* in any case to disambiguate them. 
TEXT. -/

-- QUOTE:
open bal


def b0 : bal :=       -- ∅ 
  mk_empty            

def b1 : bal :=       -- (∅)
mk_nonempty           -- constructor
  lparen.mk           -- arguments
  b0 
  rparen.mk

def b2 := 
mk_nonempty  
  lparen.mk
  b1
  rparen.mk

-- QUOTE.


/- TEXT:
You can confirm that the type of b1 is bal using the 
*check* command in Lean. The output of this  command is 
visible if you hover your cursor over the blue underline 
(in VSCode) and in your Lean infoview. You can open and
close that view in VSCode with CMD/CTRL-SHIFT-ENTER. 
TEXT. -/

-- QUOTE:
#check b1
-- QUOTE.

/- TEXT: 
You can now use the *reduce* command in Lean to see that *b1* is 
bound to the term, *mk_nonempty lparen.mk mk_empty rparen.mk*.
TEXT. -/

-- QUOTE:
#reduce b1
-- QUOTE.

/- TEXT:
From here we can build larger and larger strings in *bal*.
TEXT. -/


/- TEXT: 
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
can associate each string in our *bal* language with the 
natural number that describes its nesting depth. 

In this case, there is total function from terms of type 
*bal* to *ℕ*, so we can specify the semantics as a function
in Lean. 
TEXT. -/

-- QUOTE:
def sem : bal → ℕ 
| mk_empty := 0
| (mk_nonempty l b r) := 1 + sem b

-- We can now run some tests to see that it works
#reduce sem b0
#reduce sem b1
#reduce sem b2
-- QUOTE.

