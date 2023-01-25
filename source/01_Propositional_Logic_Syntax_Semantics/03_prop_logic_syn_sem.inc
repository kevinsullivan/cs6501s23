
*******************
Propositional Logic
*******************

Propositional logic has an infinite supply of variables.
We will represent each variable, then, as a term, var.mk
with a natural-number-valued argument. This type defines
an infinite set of terms of type *var*, each *indexed* by
a natural number. You can think of these as var₀, var₁, 
etc.  

.. code-block:: lean

  namespace cs6501
  
  inductive var : Type
  | mk : ℕ → var
  
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
  
  /-
  We can now *overload* some predefined operators in Lean
  to obtain a nice *concrete syntax* for our language. 
  -/
  #print notation ∧
  
  /- 
  Overload operators to provide a concrete syntax ("syntactic sugar")
  https://github.com/leanprover/lean/blob/master/library/init/core.lean
  -/
  
  notation (name := var_mk) `[` v `]` :=  pVar v
  notation (name := pAnd) e1 ∧ e2 :=  pAnd e1 e2
  notation (name := pOr) e1 ∨ e2 :=  pOr e1 e2
  notation (name := pNot) ¬e := pNot e
  notation (name := pImp) e1 => e2 := pImp e1 e2
  notation (name := pIff) e1 ↔ e2 := pIff e1 e2
  notation (name := pXor) e1 ⊕ e2 := pXor e1 e2
  
  
  /-
  Some examples of expressions in our concrete syntax.
  -/
  
  def X := [var.mk 0]
  def Y := [var.mk 1]
  def Z := [var.mk 2]
  
  def e1 := X ∧ Y
  def e2 := X ∨ Y
  def e3 := ¬ Z
  def e4 := e1 => e2  -- avoid overloading →
  def e5 := e1 ↔ e1
  def e6 := X ⊕ ¬X

SEMANTICS

.. code-block:: lean

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
  | (pIff e1 e2) i := biff (pEval e1 i) (pEval e2 i)
  | (pXor e1 e2) i := xor (pEval e1 i) (pEval e2 i)

