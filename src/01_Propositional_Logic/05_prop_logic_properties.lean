



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



end cs6501


