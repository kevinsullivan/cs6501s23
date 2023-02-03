/- TEXT:

**************
Satisfiability
**************

In this chapter we focus on the concepts of the satisfiability,
unsatisfiability, and validity of expressions in propositional
logic, and construct a satisfiability solver, on top of which
we then also construct unsatisfiability and validity solvers.
Here we use Lean's *import* command to include the definitions
in the file from the last class. Should you need to refer back
to such a definition, you can usually right click on the name
in VSCode and select *Go To Definition.* 
i
TEXT. -/

-- QUOTE: 
namespace cs6501
-- QUOTE.


/- TEXT:
Abstract Syntax
---------------
TEXT. -/


-- QUOTE:
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
-- QUOTE.


/- TEXT:
Concrete Syntax / Notation
--------------------------
TEXT. -/


-- QUOTE:
-- notations (concrete syntax)
def True := pLit tt
def False := pLit ff
notation (name := pVar) `[` v `]` :=  pVar v
notation (name := pNot) ¬e := pUnOp opNot e
notation (name := pAnd) e1 ∧ e2 :=  pBinOp opAnd e1 e2
notation (name := pOr) e1 ∨ e2 :=  pBinOp opOr e1 e2
notation (name := pImp) e1 ` => ` e2 := pBinOp opImp e1 e2
notation (name := pIff) e1 ↔ e2 := pBinOp opIff e1 e2
notation (name := pXor) e1 ⊕ e2 := pBinOp opXor e1 e2
-- Let's not bother with notations for nand and nor at this point
-- QUOTE.


/- TEXT: 
Semantics
---------
TEXT. -/


-- QUOTE:
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
-- QUOTE.


/- TEXT:
Formal Validation Warmup
------------------------
TEXT. -/

-- QUOTE:
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
-- QUOTE.

/- TEXT:
Testing it all out
------------------
TEXT. -/


theorem imp_trans : 
  ∀ (e1 e2 e3 : prop_expr) (i : prop_var → bool),
    (pEval (e1 => e2) i) = tt :=
begin
intros,
end


-- QUOTE.

/- TEXT: 
Exercises
---------

1. Formally state and prove that in our language, or (∨) is commutative (1 minute!)
2. Formally state and prove that in our language, not (¬) is involutive (a few minutes). 
   Hints: Put parens around (¬¬e). Open the Lean infoview with CTRL/CMD-SHIFT-RETURN/ENTER.
   If you get hung up on Lean syntax, ask a friend (or instructor) for help to get unstuck.

Solutions
---------
TEXT. -/

-- QUOTE:
end cs6501
-- QUOTE.


