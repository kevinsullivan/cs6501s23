/- TEXT:
Syntax
======

Propositional logic is the first formal language we will
study. In its simplest form it has a very simple syntax,
with the following elements:

- variables
- expressions
  - variable expressions
  - unary operator expressions
  - binary operator expressions
- sometimes two constants, *true* and *false*

The language of propositional logic is the language of
these expressions, each formed either from a variable or
by composing smaller expressions using logical operators.
-/

/-
-/

namespace cs6501

/-
Propositional logic has an infinite supply of variables.
We will represent variables -/

inductive var : Type
| mk : ℕ → var

/-
SYNTAX
-/

-- Abstract syntax
inductive pExp : Type
| pTrue : pExp
| pFalse : pExp
| pVar : var → pExp
| pNot : pExp → pExp
| pAnd : pExp → pExp → pExp
| pOr : pExp → pExp → pExp
| pImp : pExp → pExp → pExp
| pIff : pExp → pExp → pExp
| pXor : pExp → pExp → pExp 

open pExp


#print notation ∧

-- Overload operators to provide a concrete syntax ("syntactic sugar")
-- https://github.com/leanprover/lean/blob/master/library/init/core.lean
notation (name := pAnd) e1 ∧ e2 :=  pAnd e1 e2
notation (name := pOr) e1 ∨ e2 :=  pOr e1 e2
notation (name := pNot) ¬e := pNot e
notation (name := pImp) e1 => e2 := pImp e1 e2
notation (name := pIff) e1 ↔ e2 := pIff e1 e2
notation (name := pXor) e1 ⊕ e2 := pXor e1 e2

variables p1 p2 : pExp

/-
SEMANTICS
-/

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
def pEval : pExp → (var → bool) → bool
| pTrue _ := tt 
| pFalse _ := ff
| (pVar v) i := i v
| (pNot e) i := bnot (pEval e i)
| (pAnd e1 e2) i := band (pEval e1 i) (pEval e2 i) 
| (pOr e1 e2) i := bor (pEval e1 i) (pEval e2 i)
| (pImp e1 e2) i := bimp (pEval e1 i) (pEval e2 i)
| (pIff e1 e2) i := biff (pEval e1 i) (pEval e2 i)  -- HOMEWORK Solution
| (pXor e1 e2) i := xor (pEval e1 i) (pEval e2 i)

end cs6501