
import .A_06_prop_logic_algebraic_axioms 
namespace cs6501


-- 1. ⊢ ⊤                     -- true introduction
-- 2. ⊥, X ⊢ X                -- false elimination

-- 3. X, Y ⊢ X ∧ Y            -- and_introduction
-- 4. X ∧ Y ⊢ X               -- and_elimination_left
-- 5. X ∧ Y ⊢ Y               -- and_elimination_right

-- 6. X ⊢ X ∨ Y               -- or introduction left
-- 7. Y ⊢ X ∨ Y               -- or introduction right
-- 8. X ∨ Y, X → Z, Y → Z ⊢ Z -- or elimination

-- 9. ¬¬X ⊢ X                 -- negation elimination
-- 10. X → ⊥ ⊢ ¬X             -- negation introduction

-- 11. (X ⊢ Y) ⊢ (X → Y)      -- a little complicated
-- 12. X → Y, X ⊢ Y           -- arrow elimination

-- 13. X → Y, Y → X ⊢ X ↔ Y    -- iff introduction
-- 14. X ↔ Y ⊢ X → Y          -- iff elimination left
-- 15. X ↔ Y ⊢ Y → X          -- iff elimination right



/- TITLE:
Our next task is to formalize statements of these
informally stated inference rules and to prove using
Lean that these rules are logically *valid* in our 
representation of propositional logic. Doing this
will also serve as a warmup for understanding how
essentially the same inference rules are the rules
of reasoning in predicate logic. 

We first present examples, and use them to introduce
and get some practice with key ideas in Lean. Then we
leave the rest for you to prove.

Examples
--------
TEXT: -/

open cs6501 

theorem and_intro_valid : ∀ (X Y : prop_expr) (i : prop_var → bool), 
    (⟦X⟧ i = tt) → (⟦Y⟧ i = tt) → (⟦(X ∧ Y)⟧ i = tt) :=
begin
assume X Y i,
assume X_true Y_true,
unfold pEval bin_op_sem, -- axioms of eq
rw X_true,
rw Y_true,
apply rfl,
end 

theorem and_elim_left_valid : 
∀ (X Y : prop_expr) (i : prop_var → bool),
(⟦(X ∧ Y)⟧ i = tt) → (⟦X⟧ i = tt) :=
begin
unfold pEval bin_op_sem,
assume X Y i,
assume h_and,
cases ⟦ X ⟧ i,
cases ⟦ Y ⟧ i,
cases h_and,
cases h_and,
cases ⟦ Y ⟧ i,
cases h_and,
apply rfl,
end 

theorem or_intro_left_valid : 
∀ (X Y : prop_expr) (i : prop_var → bool),
(⟦(X)⟧ i = tt) → (⟦X ∨ Y⟧ i = tt) :=
begin
unfold pEval bin_op_sem,
assume X Y i,
assume X_true,
rw X_true,
apply rfl,
end

theorem or_elim_valid : ∀ (X Y Z : prop_expr) (i : prop_var → bool),
(⟦ (X ∨ Y) ⟧ i = tt) → 
(⟦ (X => Z) ⟧ i = tt) → 
(⟦ (Y => Z) ⟧ i = tt) → 
(⟦ Z ⟧ i = tt) :=
begin
-- expand definitions as assume premises
unfold pEval bin_op_sem,
assume X Y Z i,
assume h_xory h_xz h_yz,

-- the rest is by nested case analysis
-- this script is refined from my original 
cases (⟦ X ⟧ i), -- case analysis on bool (⟦ X ⟧ i) 
repeat {
  repeat {      --  case analysis on bool (⟦ Y ⟧ i)
    cases ⟦ Y ⟧ i,
    repeat {    -- case analysis on bool (⟦ Z ⟧ i)
      cases ⟦ Z ⟧ i,
      /-
      If there's an outright contradiction in your
      context, this tactic will apply false elimination
      to ignore/dismiss this "case that cannot happen."
      -/
      contradiction, 
      apply rfl,
    },
  },
},
end  






-- Write your formal propositions and proofs here: 



end cs6501
