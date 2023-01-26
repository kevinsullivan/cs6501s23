
*******************
Propositional Logic
*******************

Propositional logic has an infinite supply of variables.
We will represent each variable, then, as a term, var.mk
with a natural-number-valued argument. This type defines
an infinite set of terms of type *prop_var*, each *indexed* 
by a natural number. You can think of these as var₀, var₁, 
etc.  

.. code-block:: lean

  namespace cs6501
  
  -- variables, indexed by natural numbers
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

We can now *overload* some predefined operators in Lean
having appropriate associativity and precedence properties
to obtain a nice *concrete syntax* for our language. See also
(https://github.com/leanprover/lean/blob/master/library/init/core.lean)

.. code-block:: lean

  notation (name := var_mk) `[` v `]` :=  pVar v
  notation (name := pAnd) e1 ∧ e2 :=  pAnd e1 e2
  notation (name := pOr) e1 ∨ e2 :=  pOr e1 e2
  notation (name := pNot) ¬e := pNot e
  notation (name := pImp) e1 => e2 := pImp e1 e2
  notation (name := pIff) e1 ↔ e2 := pIff e1 e2
  notation (name := pXor) e1 ⊕ e2 := pXor e1 e2

Here, after giving nice names, X, Y, and Z, to
the first three variables, we givesome examples of 
propositional logic expressions written using our
new *concrete* syntax.

.. code-block:: lean

  def X := [prop_var.mk 0]
  def Y := [prop_var.mk 1]
  def Z := [prop_var.mk 2]
  
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

I'll fill in explanatory text later, but for now wanted
to get you the *code*.
