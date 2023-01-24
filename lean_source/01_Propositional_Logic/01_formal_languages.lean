/- TEXT:
Formal Languages : Syntax and Semantics
=======================================

To begin our journey into the formalization of abstract
mathematics for software engineering, we will specify the 
syntax and semantics of a very simple mathatical language, 
namely *propositional logic*. 

*Propositional logic* is *isomorphic* to (essentially 
the same thing as) Boolean algebra. You already know about 
Boolean algebra from writing conditions in *if* and *loop* 
commands in everyday programming languages such as Java.  

Our task is to see how to formalize the syntax and semantics
of this language in Lean. As a warmup, and to put some basic
concepts into play, however, we will first specify the syntax 
and semantics of a simpler formal language: the language of
strings of balanced parentheses. So let's get started.

Formal languages
----------------

The syntax of propositional logic defines a *formal language:* 
a (possibly infinite) set of strings of symbols from a given 
*alphabet*. The formal language of basic algebra, for example, 
includes strings such as *x*, *y*, and *x + y*, but not *x y*,
while propositional logic includes *X*, *Y*, and *X ∧ Y* but
not *X Y*. 

As another example, consider the formal language of all strings 
of balanced parentheses. The language include the empty string, 
*(), (()), ((())), ...., ad infinitum,* but not *(*, *)*, *(()*
and so forth. 

What we need first is a complete and precise way to specify all 
and only the strings in such a language. One way to do this is 
to give a *finite* set of *rules* for building all and only the 
strings in of a given langauge language.

We can specify the balanced parentheses language with just two
rules. First, the empty string, denoted ∅, is an string in the 
language. Second, if *e* is *any* string in the language, then 
so is *(e)*, i.e., *e* inside another pair of parentheses. 

We can obtain a string of any nesting depth in this language
by applying the first rule once then the second rule as many
(but a finite) times as needed to obtain the desired string. The
length of each such string is finite but the number of strings 
in the language is infinite. 

Syntax
------

We can write this set of rules somewhat more formally as
a *grammar* expressed in so-called *Backus-Naur Form*, or
BNF, as follows: 

  *expression ::= 
  | ∅ 
  | (expression)*. 

This definition says that an expression (string) in our
language is either the empty string or it's an expression
within a pair of parentheses. That's it. 

You can see that the strings *generated* by this grammar 
include the empty string, and any longer string of balanced 
parentheses. It isn't possible with these rules to produce 
a string with unbalanced parentheses. So we have a grammar
for the language we've described informally up to now. 

Next we give an equivalent and *completely formal* definition
of this language in Lean. 

Inductive Data Type Definitions
-------------------------------

In this case, we'll start by defining separate data 
types, each with just one value, to represent left and 
right parentheses, respectively. The names of the type
are lparen and rparen and each has a single value that
we will call *mk*. We can also say that *mk* in the one
parameterless (constant) value (or *term*) of this type.
TEXT. -/


-- QUOTE:

inductive lparen 
| mk

inductive rparen
| mk
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

-- QUOTE:
def b2 : bal :=   -- construct this larger string in bal ...
mk_nonempty 
  lparen.mk 
  b1              -- ... from this smaller string in bal
  rparen.mk
-- QUOTE.

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

