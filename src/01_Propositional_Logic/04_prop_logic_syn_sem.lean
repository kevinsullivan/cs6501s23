

namespace cs6501

-- variables, still indexed by natural numbers
inductive prop_var : Type
| mk (n : ℕ)

-- examples
def v₀ := prop_var.mk 0
def v₁ := prop_var.mk 1
def v₂ := prop_var.mk 2


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


def op_sem : binop → (bool → bool → bool)
| opAnd := band 
| opOr  := bor
| opImp := bimp
| opIff := biff
| opXor := bxor

-- A quick demo
#reduce ((op_sem opAnd) tt ff)
#reduce (op_sem opOr tt ff) -- recall left associativity


def pEval : prop_expr → (prop_var → bool) → bool
| (pLit b)          i := b 
| ([v])             i := i v                  -- our [] notation on the left
| (¬e)              i := bnot (pEval e i)     -- our ¬ notation; Lean's bnot
| (pBinOp op e1 e2) i := (pEval e1 i) && (pEval e2 i) -- BUG!


end cs6501