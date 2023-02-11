
/- TEXT:

**********************
A Better Specification
**********************

In this chapter we present an improved specification
of the syntax and semantics of propositional logic. As
usual, we first present the syntax specification then the
semantics.

Syntax
------
TEXT. -/

namespace cs6501

-- QUOTE:
-- variables, still indexed by natural numbers
inductive prop_var : Type
| mk (n : ℕ)

-- examples
def v₀ := prop_var.mk 0
def v₁ := prop_var.mk 1
def v₂ := prop_var.mk 2
-- QUOTE. 

/- TEXT:
We will now refactor our definition of 
prop_expr to factor out mostly repeated code 
and to make explicit (1) a class of *literal*
expressions, and (2) binary operators as first
class citizens and a class of corresponding
binary operator expressions. Be sure to compare
and contrast our definitions here with the ones in
the last chapter.

We'll start by defining a *binary operator* type
whose values are abstract syntax terms for binary
operators/connectives in propositional logic.
TEXT. -/

-- QUOTE:
-- Syntactic terms for binary operators
inductive binop
| opAnd
| opOr
| opImp
| opIff
| opXor

open binop

-- A much improved language syntax spec
inductive prop_expr : Type
| pLit (b : bool)                         -- literal expressions
| pVar (v: prop_var)                      -- variable expressions
| pNot (e : prop_expr)                    -- unary operator expression
| pBinOp (op : binop) (e1 e2 : prop_expr) -- binary operator expressions

open prop_expr


-- An example of an "and" expression
def an_and_expr := 
  pBinOp 
    opAnd                   -- binary operator
    (pVar (prop_var.mk 0))  -- variable expression
    (pVar (prop_var.mk 1))  -- variable expression
-- QUOTE.

/- TEXT:
We have to update the previous notations definitions,
which now need to *desugar* to use the new expression
constructors. We also define some shorthands for the
two literal expressions in our language.
TEXT. -/


-- QUOTE:
def True := pLit tt
def False := pLit ff
notation (name := pVar) `[` v `]` :=  pVar v
notation (name := pAnd) e1 ∧ e2 :=  pBinOp opAnd e1 e2
notation (name := pOr) e1 ∨ e2 :=  pBinOp opOr e1 e2
notation (name := pNot) ¬e := pNot e
notation (name := pImp) e1 => e2 := pBinOp opImp e1 e2
notation (name := pIff) e1 ↔ e2 := pBinOp opIff e1 e2
notation (name := pXor) e1 ⊕ e2 := pBinOp opXor e1 e2

-- Precedence highest to lowest NOT, NAND, NOR, AND, OR, ->, ==
-- `↓`:37 x:37
reserve notation `↓`:37 x:37
notation (name := pNor) e1 `↓` e2 := pBinOp opAnd e1 e2

#print notation ¬ 
#print notation ∧ 
#print notation ↑
#print notation ↓ 

-- QUOTE.


/- TEXT:
Here are examples of expressions using our concrete syntax
TEXT. -/

-- QUOTE:
-- variable expressions from variables
def X := [v₀]
def Y := [v₁]
def Z := [v₂]

-- operator expressions
def e1 := X ∧ Y
def e2 := X ∨ Y
def e3 := ¬Z
def e4 := e1 => e2
def e5 := e1 ↔ e1
def e6 := X ⊕ ¬X
-- QUOTE.

/- TEXT:
Semantics
---------

A benefit of having made binary operators 
explicit as a set of syntactic terms is that
we can simultaneously simplify and generalize 
our semantics. 
TEXT. -/

-- QUOTE:
-- Helper functions
def bimp : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := tt
| ff ff := tt

def biff : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := ff
| ff ff := tt
-- QUOTE.

/- TEXT:
We now define an *interpretation* for operator symbols!
Each binop (a syntactic object) has as its meaning some
corresponding binary Boolean operator.
TEXT. -/

-- QUOTE:
def op_sem : binop → (bool → bool → bool)
| opAnd := band 
| opOr  := bor
| opImp := bimp
| opIff := biff
| opXor := bxor

-- A quick demo
#reduce ((op_sem opAnd) tt ff)
#reduce (op_sem opOr tt ff) -- recall left associativity
-- QUOTE.

/- TEXT:
Now here's a much improved semantic specification.
In place of rules for pTrue and pFalse we just have
one rule for pLit (literal expressions). Second, in
place of one rule for each binary operator we have
one rule for *any* binary operator. 
TEXT. -/

-- QUOTE:
def pEval : prop_expr → (prop_var → bool) → bool
| (pLit b)          i := b 
| ([v])             i := i v                  -- our [] notation on the left
| (¬e)              i := bnot (pEval e i)     -- our ¬ notation; Lean's bnot
| (pBinOp op e1 e2) i := (pEval e1 i) && (pEval e2 i) -- BUG!
-- QUOTE.

/- TEXT:

Exploration
-----------

You've heard about Lean and seen in it action, but there's no substitute for
getting into it yourself. The goal of this exploration is for you to "connect 
all the dots" in what we've developed so far, and for you to start to develop 
"muscle memory" for some basic Lean programming. 

  - Identify and fix the bug in the last rule of pEval
  - Replace pNot with pUnOp ("unary operator"), as with pBinOp
  - Add end-to-end support for logical *nand* (↑) and *nor* (↓) expression-building operators
  - Define some examples of propositional logic expressions using concrete syntax
  - Define several interpretations and evaluate each of your expressions under each one

To avoid future git conflicts, make a copy of src/04_prop_logic_syn_sem.lean, and 
make changes to that file rather than to the original. Bring your completed work 
to our next class. Be prepared to share and/or turn in your work at the beginning
of next class.

TEXT. -/

end cs6501