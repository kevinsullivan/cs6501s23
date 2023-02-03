/- TEXT:

***************************
Homework: Formal Validation
***************************

In class today, as evidenced by the developments in 
the first section, below, we saw that it's not enough
to prove a few theorems about a construction (here our
syntax and semantics for propositional logic). One has
to prove that a construction has *all* of the properties
of the concept it's meant to represent.

Improved Specification
----------------------
TEXT. -/


-- QUOTE:
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
-- QUOTE.


/- TEXT: 
The *semantic domain* for our language is not only the
Boolean values, but also the Boolean operations. We map
variables to Boolean values via an *interpretation* and
we define a fixed mapping of logical connectives (¬, ∧, 
∨, etc.) to Boolean operations (bnot, band, bor, etc.)

With these elementary semantic mappings in place we can
finally now *any* propositional logical expression to 
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
TEXT. -/


-- QUOTE:
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
-- QUOTE.


/- TEXT:
Formal Validation
----------------- 

The intended intuitive meaning of *and* in propositional
logic is that both of its argument expresions are true,
and that is all. To have this meaning requires that *and
is commutative*. By that phrase we mean that the formula
e1 ∧ e2 always means the same as e2 ∧ e1.

To be precise we formalize this requirement with the
following proposition, and_commutes, which we then prove.
TEXT. -/

-- QUOTE:
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
-- QUOTE.

/- TEXT:
Homework
--------

Wow, we know that bimp is buggy and yet we were able
to prove both of these properties about it. Right! To
fully validate, and thus *know for sure* that our logic 
correctly simulates propositional logic, we need to prove
that *all* of the essential properties of the logic hold
for our representation. 

Here's a set of rules that's more complete. You job is 
to formally state each rule then prove that it holds in 
our logic. As you do this, identify the rule(s) that 
can't be proved due to the fault in our specification, 
bimp, of the Boolean implication operation.

We present these rules in the form of sequents. Express 
each of the rules in our logic by replacing turnstiles
(⊢) with implies (=>), and commas (,) with and (∧). Use
parenthesis pairs to specify grouping explicitly if you're
unsure of precendence and/or associativity. Then prove 
that each formula is true, for *all* expressions, X, Y, 
and Z, and *all* interpretations/assignments-of-values, 
*i,* for X, Y, and Z.
TEXT. -/

-- QUOTE:
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
-- QUOTE.

/- TEXT:
In the style we've developed, formally state and prove 
that our logic and semantics has each of the properties, 
1, 2, 4, 5, 6, 8, 9, 10, 12, and 15. Identify any rules 
that fail to be provable due to the injected bug in bimp.

Use Lean's *theorem* directive to give names to proofs. 
as names for your proofs, use the names in the comments
after each rule (adding missing underscores as needed).

To do this part of the assignment, make a copy of this
file from the class repo and add the statement and proof
of each theorem below. You will turn in the file with these
proofs included in the given order at the end of the file.

This isn't a comprehensive list of properties. We lack
rules for ⊤ and ⊥ (formerly True, False; still terms 
that invariably evaluate to true (tt) and false (ff).
There are rules that explain, for example, that ⊤ ∧ e 
is equivalent to e; ⊥ ∧ e is invariably false; ⊥ or e 
is equivalent to e; and ⊤ ∨ e is invariably true. Go 
ahead and prove these propositions as well if you just
can't stop proving! (optional :-).

Try to do all or at least most of this assignment on 
your own. Feel free to ask for or give help on minor
matters, e.g., of Lean syntax, or if some concept isn't
yet clear enough. Discussing such issues is constructive. 
I skipped over properties whose proofs look almost just
like those for closely related properties.
TEXT. -/
-- QUOTE:
end cs6501
-- QUOTE.
