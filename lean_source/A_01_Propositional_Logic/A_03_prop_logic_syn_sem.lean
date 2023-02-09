
/- TEXT:

*******************
Propositional Logic
*******************

In this chapter, we'll present a first
version of a syntax and semantic specification
for a full language of propositional logic. As
in the last chapter, we start by defining the
syntax, then we present the semantics.

Syntax
------
TEXT. -/

namespace cs6501

-- QUOTE:
/-
Propositional logic has an infinite supply of variables.
We will represent each variable, then, as a term, var.mk
with a natural-number-valued argument. This type defines
an infinite set of terms of type *prop_var*, each *indexed* 
by a natural number.   
-/
inductive prop_var : Type
| mk (n : ℕ)

-- Abstract syntax
inductive prop_expr : Type
| pTrue : prop_expr
| pFalse : prop_expr
| pVar (v: prop_var) 
| pNot (e : prop_expr) 
| pAnd (e1 e2 : prop_expr)
| pOr (e1 e2 : prop_expr)
| pImp (e1 e2 : prop_expr)
| pIff (e1 e2 : prop_expr)
| pXor (e1 e2 : prop_expr) 

open prop_expr
-- QUOTE.

/- TEXT:
We can now *overload* some predefined operators in Lean
having appropriate associativity and precedence properties
to obtain a nice *concrete syntax* for our language. See also
(https://github.com/leanprover/lean/blob/master/library/init/core.lean)
TEXT. -/

-- QUOTE:
notation (name := var_mk) `[` v `]` :=  pVar v
notation (name := pAnd) e1 ∧ e2 :=  pAnd e1 e2
notation (name := pOr) e1 ∨ e2 :=  pOr e1 e2
notation (name := pNot) ¬e := pNot e
notation (name := pImp) e1 => e2 := pImp e1 e2
notation (name := pIff) e1 ↔ e2 := pIff e1 e2
notation (name := pXor) e1 ⊕ e2 := pXor e1 e2
-- QUOTE.

/- TEXT:
Here, after giving nice names, X, Y, and Z, to
the first three variables, we givesome examples of 
propositional logic expressions written using our
new *concrete* syntax.
TEXT. -/

-- QUOTE:
def X := [prop_var.mk 0]
def Y := [prop_var.mk 1]
def Z := [prop_var.mk 2]

def e1 := X ∧ Y
def e2 := X ∨ Y
def e3 := ¬ Z
def e4 := e1 => e2  -- avoid overloading →
def e5 := e1 ↔ e1
def e6 := X ⊕ ¬X
-- QUOTE.

/- TEXT:
Semantics
---------
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

-- Operational semantics
def pEval : prop_expr → (prop_var → bool) → bool
| pTrue _ := tt 
| pFalse _ := ff
| ([v]) i := i v
| (¬ e) i := bnot (pEval e i)
| (e1 ∧ e2) i := (pEval e1 i) && (pEval e2 i) 
| (e1 ∨ e2) i := (pEval e1 i) || (pEval e2 i)
| (e1 => e2) i := bimp (pEval e1 i) (pEval e2 i)
| (e1 ↔ e2) i := biff (pEval e1 i) (pEval e2 i)
| (e1 ⊕ e2) i := xor (pEval e1 i) (pEval e2 i)
-- QUOTE.

/- TEXT:
I'll fill in explanatory text later, but for now wanted
to get you the *code*.
TEXT. -/

end cs6501