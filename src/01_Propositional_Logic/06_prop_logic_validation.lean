

namespace cs6501

inductive prop_var : Type
| mk (n : ℕ)

inductive unop 
| opNot

inductive binop
| opAnd
| opOr
| opImp
| opIff
| opXor

open unop
open binop

inductive prop_expr : Type
| pLit (b : bool)                         -- literal expressions
| pVar (v: prop_var)                      -- variable expressions
| pUnOp (op :unop) (e : prop_expr)                    -- unary operator expression
| pBinOp (op : binop) (e1 e2 : prop_expr) -- binary operator expressions

open prop_expr

notation ` ⊤ ` := pLit tt   -- Notation for True
notation ` ⊥ ` := pLit ff   -- Notation for False
notation (name := pVar) `[` v `]` :=  pVar v
notation (name := pNot) ¬e := pUnOp opNot e
notation (name := pAnd) e1 ∧ e2 :=  pBinOp opAnd e1 e2
notation (name := pOr) e1 ∨ e2 :=  pBinOp opOr e1 e2
precedence ` => `: 50                                      -- add operator precedence
notation (name := pImp) e1 `=>`  e2 := pBinOp opImp e1 e2  -- bug fixed; add back quotes
notation (name := pIff) e1 ↔ e2 := pBinOp opIff e1 e2
notation (name := pXor) e1 ⊕ e2 := pBinOp opXor e1 e2




-- implication 
-- this specification is intentionally buggy
def bimp : bool → bool → bool
| tt tt := tt
| tt ff := tt
| ff tt := ff
| ff ff := tt

-- bi-implication
def biff : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := ff
| ff ff := tt

def un_op_sem : unop → (bool → bool)
| opNot := bnot 

def bin_op_sem : binop → (bool → bool → bool)
| opAnd := band 
| opOr  := bor
| opImp := bimp
| opIff := biff
| opXor := bxor

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


-- ∨ is commutative
def or_commutes : 
  ∀ (e1 e2 : prop_expr) 
    (i : prop_var → bool),
    (pEval (e1 ∨ e2) i) = (pEval (e2 ∨ e1) i) :=
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

-- negation (not) is involutive
theorem not_involutive: ∀ e i, (pEval e i) = (pEval (¬¬e) i) :=
begin
assume e i,
unfold pEval,
unfold un_op_sem,
cases (pEval e i),
repeat { apply rfl },
end

-- implication is transitive
theorem imp_trans : 
  ∀ (e1 e2 e3 : prop_expr) (i : prop_var → bool),
    (pEval (e1 => e2) i) = tt → 
    (pEval (e2 => e3) i) = tt →
    (pEval (e1 => e3) i) = tt :=
begin
unfold pEval,
unfold bin_op_sem,
assume e1 e2 e3 i h12 h23,
cases (pEval e1 i),
cases (pEval e2 i),
cases (pEval e3 i),
-- first 4 cases for e1
assumption, --"exact rfl" will also work
assumption,
cases (pEval e3 i),
assumption,
assumption,
-- second four cases for e1
cases (pEval e2 i),
cases (pEval e3 i),
assumption,
assumption,
cases (pEval e3 i),
assumption,
assumption,
end

-- contrapositive: (X => Y) → (¬Y => ¬X)
/-
Example: if whenever it rains (X) the ground gets 
wet (Y), then if the ground is NOT wet then is can't 
have rained. Can we prove this principle to be valid
in our logic? 
-/
theorem contrapos : 
∀ (e1 e2 : prop_expr) 
  (i : prop_var → bool),
  (pEval (e1 => e2) i) = tt → 
  (pEval (¬e2 => ¬e1)) i = tt :=
begin
assume e1 e2 i,
unfold pEval,
unfold un_op_sem bin_op_sem,    
cases (pEval e1 i),
cases (pEval e2 i),
unfold bnot bimp,
assume h,
assumption,
unfold bnot bimp,
assume h,
assumption,
cases (pEval e2 i),
unfold bnot bimp,
assume h,
assumption,
unfold bnot bimp,
assume h,
assumption,
end


-- 1. X, Y ⊢ X ∧ Y            -- and_introduction
-- 2. X ∧ Y ⊢ X               -- and_elimination_left
-- 3. X ∧ Y ⊢ Y               -- and_elimination_right
-- 4. ¬¬X ⊢ X                 -- negation elimination 
-- 5. ¬(X ∧ ¬X)               -- no contradiction
-- 6. X ⊢ X ∨ Y               -- or introduction left
-- 7. Y ⊢ X ∨ Y               -- or introduction right
-- 8. X ∨ Y, X → Z, Y → Z ⊢ Z -- or elimination
-- 9. X → Y, Y → X ⊢ X ↔ Y    -- iff introduction
-- 10. X ↔ Y ⊢ X → Y          -- iff elimination left
-- 11. X ↔ Y ⊢ Y → X          -- iff elimination right
-- 12. X → Y, X ⊢ Y           -- arrow elimination
-- 13. X → Y, Y → Z ⊢ X → Z   -- transitivity of arrow 
-- 14. X → Y ⊢ ¬Y → ¬X        -- contrapositive
-- 15. ¬(X ∨ Y) ↔ ¬X ∧ ¬Y     -- DeMorgan 1 (¬ over ∨)
-- 16. ¬(X ∧ Y) ↔ ¬X ∨ ¬Y     -- Demorgan 2 (¬ over ∧)

end cs6501
