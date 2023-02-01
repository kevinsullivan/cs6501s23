
*****************
Formal Validation
*****************

So far we've defined (1) an abstract syntax for propositional
logic, (2) a "big step" operational semantics for our syntax, 
and (3) a concrete syntax for it, in the form of prefix (¬) and
infix (∧, ∨, =>, etc) operators. 

But how do we know that our *specification* is correct? Checking
a specification for correctness is called *validating* it, or just
validation. *Formal* validation is the use of mathematical logic
to validate given specifications.

In particular, one can formally validate a specification by
proving that it has certain required properties. To illustrate
the point, n this chapter we add a fourth section,(4): a formal 
proof of the proposition that in our syntax and semantics, ∧ is 
commutative; that for *any* expressions in propositional logic, 
e1 and e2, and for *any* interpretation, the values of e1 ∧ e2 
under i, and of e2 ∧ e1 under i, are equal.  

Another way to look at this chapter is that it extends the set of 
elements of a good formalization of a mathematical concept from 
three above to four. Now the modular unit of definition specifies 
(1) the data (sometimes language syntax, sometimes not), (2) the 
operations on that data, (3) the available concrete notations, 
and now also (4) proofs that essential properties hold. 

.. code-block:: lean

  
  namespace cs6501


Abstract Syntax
---------------


.. code-block:: lean

  
  -- variables, indexed by natural numbers
  inductive prop_var : Type
  | mk (n : ℕ)
  
  -- Abstract syntactic terms for unary operators
  inductive unop 
  | opNot
  
  -- Abstract syntactic terms for binary operators
  inductive binop
  | opAnd
  | opOr
  | opImp
  | opIff
  | opXor
  
  -- make constructor names globally visible
  open unop
  open binop
  
  -- syntax
  inductive prop_expr : Type
  | pLit (b : bool)                         -- literal expressions
  | pVar (v: prop_var)                      -- variable expressions
  -- | pNot (e : prop_expr)                    -- unary operator expression
  | pUnOp (op :unop) (e : prop_expr)                    -- unary operator expression
  | pBinOp (op : binop) (e1 e2 : prop_expr) -- binary operator expressions
  
  open prop_expr
  


Concrete Syntax / Notation
--------------------------


.. code-block:: lean

  
  -- notations (concrete syntax)
  def True := pLit tt
  def False := pLit ff
  notation (name := pVar) `[` v `]` :=  pVar v
  notation (name := pNot) ¬e := pUnOp opNot e
  notation (name := pAnd) e1 ∧ e2 :=  pBinOp opAnd e1 e2
  notation (name := pOr) e1 ∨ e2 :=  pBinOp opOr e1 e2
  notation (name := pImp) e1 => e2 := pBinOp opImp e1 e2
  notation (name := pIff) e1 ↔ e2 := pBinOp opIff e1 e2
  notation (name := pXor) e1 ⊕ e2 := pBinOp opXor e1 e2
  -- Let's not bother with notations for nand and nor at this point


Semantics
---------


.. code-block:: lean

  
  -- Boolean implication operation 
  def bimp : bool → bool → bool
  | tt tt := tt
  | tt ff := tt
  | ff tt := ff
  | ff ff := tt
  
  -- Boolean biimplication operation
  def biff : bool → bool → bool
  | tt tt := tt
  | tt ff := ff
  | ff tt := ff
  | ff ff := tt
  
  -- interpretations of binary operators
  def bin_op_sem : binop → (bool → bool → bool)
  | opAnd := band 
  | opOr  := bor
  | opImp := bimp
  | opIff := biff
  | opXor := bxor
  
  -- interpretations of unary operators
  def un_op_sem : unop → (bool → bool)
  | opNot := bnot 
  
  -- semantic evaluation (meaning of expressions)
  def pEval : prop_expr → (prop_var → bool) → bool
  | (pLit b)          i := b 
  | ([v])             i := i v                  -- our [] notation on the left
  | (pUnOp op e)      i := (un_op_sem op) (pEval e i)     -- our ¬ notation; Lean's bnot
  | (pBinOp op e1 e2) i := (bin_op_sem op) (pEval e1 i) (pEval e2 i) -- BUG FIXED :-)!


Formal Validation
----------------- 


.. code-block:: lean

  
  -- proof of one key property: "commutativity of ∧" in the logic we've specified,, as required
  def and_commutes : 
    ∀ (e1 e2 : prop_expr) 
      (i : prop_var → bool),
      (pEval (e1 ∧ e2) i) = (pEval (e2 ∧ e1) i) :=
  begin
  assume e1 e2 i,
  unfold pEval,
  unfold bin_op_sem,
  cases (pEval e1 i),
  cases (pEval e2 i),
  apply rfl,
  apply rfl,
  cases (pEval e2 i),
  apply rfl,
  apply rfl,
  end 
  

Testing it all out
------------------

.. code-block:: lean

  
  -- tell Lean to explain given notations
  #print notation ¬ 
  #print notation ∧ 
  #print notation ↑
  
  -- variables
  def v₀ := prop_var.mk 0
  def v₁ := prop_var.mk 1
  def v₂ := prop_var.mk 2
  
  -- variable expressions
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
  
  -- an interpretation
  def an_interp : prop_var → bool
  | (prop_var.mk 0) := tt -- X
  | (prop_var.mk 1) := ff -- Y
  | (prop_var.mk 2) := tt -- Z
  | _ := ff               -- any other variable
  
  -- evaluation 
  #reduce pEval X an_interp  -- expect false
  #reduce pEval Y an_interp  -- expect false
  #reduce pEval e1 an_interp  -- expect false
  
  -- applying theorem!
  #reduce and_commutes X Y an_interp
  -- result is a proof that ff = ff
  

Exercises
---------

1. Formally state and prove that in our language, or (∨) is commutative (1 minute!)
2. Formally state and prove that in our language, not (¬) is involutive (a few minutes). 
   Hints: Put parens around (¬¬e). Open the Lean infoview with CTRL/CMD-SHIFT-RETURN/ENTER.
   If you get hung up on Lean syntax, ask a friend (or instructor) for help to get unstuck.

Solutions
---------


.. code-block:: lean

  end cs6501

