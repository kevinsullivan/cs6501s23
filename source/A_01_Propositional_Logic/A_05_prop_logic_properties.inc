
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
Abstract Syntax
---------------

.. code-block:: lean

  namespace cs6501
  
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
  notation ` ⊤ ` := pLit tt   -- Notation for True
  notation ` ⊥ ` := pLit ff   -- Notation for False
  def True := pLit tt         -- deprecated now
  def False := pLit ff        -- deprecated now
  notation (name := pVar) ` [ ` v  ` ] ` :=  pVar v
  notation (name := pNot) ¬e := pUnOp opNot e
  notation (name := pAnd) e1 ` ∧ ` e2 :=  pBinOp opAnd e1 e2
  notation (name := pOr) e1 ` ∨ ` e2 :=  pBinOp opOr e1 e2
  precedence ` => `: 23                                        -- add operator precedence
  notation (name := pImp) e1 ` => `  e2 := pBinOp opImp e1 e2  -- bug fixed; add back quotes
  notation (name := pIff) e1 ` ↔ ` e2 := pBinOp opIff e1 e2
  notation (name := pXor) e1 ` ⊕ ` e2 := pBinOp opXor e1 e2
  -- Let's not bother with notations for nand and nor at this point

Semantics
---------

The *semantic domain* for our language is not only the
Boolean values, but also the Boolean operations. We map
variables to Boolean values (via an interpretation) and
we define a fixed mapping of logical connectives (¬, ∧, 
∨, etc.) to Boolean operations (bnot, band, bor, etc.)
With these elementary semantic mappings in place we can
finally map *any* propositional logical expression to 
its (Boolean) meaning in a *compositional* manner, where
the meaning of any compound expression is composed from
the meanings of its parts, which we compute recursively,
down to individual variables and connectives.

The Lean standard libraries define some but not all 
binary Boolean operations. We will thus start off in 
this section by augmenting Lean's definitions of the
Boolean operations with two more: for implication (we
follow Lean naming conventions and call this bimp) and
bi-implication (biff).

.. code-block:: lean

  -- Boolean implication operation (buggy!)
  def bimp : bool → bool → bool
  | tt tt := tt
  -- A fault to inject first time through
  -- Now corrected in following to lines
  -- | tt ff := tt
  -- | ff tt := ff
  | tt ff := ff
  | ff tt := tt
  | ff ff := tt
  
  -- Boolean biimplication operation
  def biff : bool → bool → bool
  | tt tt := tt
  | tt ff := ff
  | ff tt := ff
  | ff ff := tt

Next we define a fixed interpretation for our
syntactic logical connectives, first unary and
then binary. We give these mappings in the form
of functions from unary and binary operators
(which act to compose logical expressions into
new expressions), to Boolean operations (which 
compose Boolean values into Boolean results). 

.. code-block:: lean

  -- interpretations of unary operators
  def un_op_sem : unop → (bool → bool)
  | opNot := bnot 
  
  -- interpretations of binary operators
  def bin_op_sem : binop → (bool → bool → bool)
  | opAnd := band 
  | opOr  := bor
  | opImp := bimp
  | opIff := biff
  | opXor := bxor

And now here's our overal expression semantic evaluation
function. It works as described, computing the value of 
sub-expressions and composing the Boolean results into
final Boolean meanings for any given expression under any
give interpretation.

.. code-block:: lean

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
  -- assume that e1 e2 and i are arbitrary
  assume e1 e2 i,
  
  -- unfold definition of pEval for given arguments
  unfold pEval,
  
  -- unfold definition of bin_op_sem
  unfold bin_op_sem,
  
  -- case analysis on Boolean value (pEval e1 i)
  cases (pEval e1 i),
  
  -- within first case, nested case analysis on (pEval e2 i)
  cases (pEval e2 i),
  
  -- goal proved by reflexivity of equality
  apply rfl,
  
  -- second case for (pEval e2 i) within first case for  (pEval e1 i)
  apply rfl,
  
  -- onto second case for (pEval e1 i)
  -- again nested case analysis on (pEval e2 i)
  cases (pEval e2 i),
  
  -- and both cases are again true by reflexivity of equality 
  apply rfl,
  apply rfl,
  -- QED
  end 

Examples
--------

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
  #reduce pEval (X => Y) an_interp  -- oops
  
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

  
  -- The proof that ∨ is commutative is basically identical to that for ∧
  def or_commutes : 
    ∀ (e1 e2 : prop_expr) 
      (i : prop_var → bool),
      (pEval (e1 ∨ e2) i) = (pEval (e2 ∨ e1) i) :=
  begin
  -- Suppose e1 e2 and i are arbitrary expressions and interpretation
  assume e1 e2 i,
  -- unfold definitions of pEval and bin_op_sem applied to their arguments
  unfold pEval,
  unfold bin_op_sem,
  -- proof by simple case analysis on possible results of evaluating e1 and e2 under i
  cases (pEval e1 i),
  cases (pEval e2 i),
  apply rfl,
  apply rfl,
  cases (pEval e2 i),
  apply rfl,
  apply rfl,
  -- QED: By showing it's true for arbitrary e1/e2/i we've shown it's true for *all* 
  end 
  
  -- Prove not is involutive
  theorem not_involutive: ∀ e i, (pEval e i) = (pEval (¬¬e) i) :=
  begin
  assume e i,
  unfold pEval,
  unfold un_op_sem,
  cases (pEval e i),
  repeat { apply rfl },
  end
  
  end cs6501

