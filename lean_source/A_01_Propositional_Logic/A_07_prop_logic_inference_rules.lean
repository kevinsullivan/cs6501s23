/- TEXT:

***************
Inference Rules
***************

In this chapter we will present another approach 
to validating our model of propositional logic: by 
verifying that it satisifies the *inference rules* 
of this logic.

An inference rule is basically a function that takes 
zero or more arguments, usually including what we call
*truth judgements* or *proofs* of certain propositions,
and that returns truth judgments or proofs of other
propositions, which are said to be *derived* or to be
*deduced* from the arguments. 

For example, in both propositional and *first-order
predicate* logic, we have a rule, *and introduction*,
that takes as arguments, or *premises*, truth judgments 
for any two arbitrary propositions, *X* and *Y*, and 
that returns a truth judgment for *X ∧ Y*. 

A truth judgment is a determination that a proposition,
say *X*, is logically true, and can be written (in paper
and pencil logic as) *X : true*. The *and introduction*
rule thus states that *X : True, Y : True ⊢ X ∧ Y : True.*

This is usually shortened to *X, Y ⊢ X ∧ Y* based on the
assumption that everything to the left of the turnstile
is assumed to have already been judged to be true. Such
a rule can be pronounced as follows: in a context in which
you have already judged X and Y to be true you can always
conclude that X ∧ Y is true.

What's different is that these rules are syntactic and
don't presume that we have an algorithm for determining
truth, as we do with propositional logic, but not for
predicate logic. 

TEXT. -/

-- QUOTE:
import .A_06_prop_logic_algebraic_axioms 
namespace cs6501
-- QUOTE.

/- TEXT:
Inference Rules
---------------

Key idea: These are rules for reasoning about evidence.
What *evidence* do you need to derive a given conclusion?
These are the "introduction" rules. From a given piece of
evidence (and possibly with additional evidence) what new
forms of evidence can you derive? These are "elimination"
rules of the logic.
TEXT. -/

-- QUOTE:
-- 1. ⊢ ⊤                     -- true introduction
-- 2. ⊥, X ⊢ X                -- false elimination

-- 3. X, Y ⊢ X ∧ Y            -- and_introduction
-- 4. X ∧ Y ⊢ X               -- and_elimination_left
-- 5. X ∧ Y ⊢ Y               -- and_elimination_right

-- 6. X ⊢ X ∨ Y               -- or introduction left
-- 7. Y ⊢ X ∨ Y               -- or introduction right
-- 8. X ∨ Y, X → Z, Y → Z ⊢ Z -- or elimination

-- 9. ¬¬X ⊢ X                 -- negation elimination
-- 10. X → ⊥ ⊢ ¬X              -- negation introduction

-- 11. (X ⊢ Y) → (X → Y)      -- a little complicated
-- 12. X → Y, X ⊢ Y           -- arrow elimination

-- 13. X → Y, Y → X ⊢ X ↔ Y    -- iff introduction
-- 14. X ↔ Y ⊢ X → Y          -- iff elimination left
-- 15. X ↔ Y ⊢ Y → X          -- iff elimination right

-- QUOTE.

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
unfold pEval bin_op_sem,
assume X Y Z i,
assume h_xory h_xz h_yz,
-- case analysis
-- you do the rest!
end  

/- TEXT:

Practice
--------

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
