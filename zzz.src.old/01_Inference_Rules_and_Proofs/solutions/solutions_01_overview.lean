/-

As a reminder, here are the inference rules (and a few
"logical fallacies" that you tested for validity in the
setting of propositional logic. 

In this next section of class, we 'll see that enhanced
versions of these inference rules serve as foundations
for valid reasoning about the truth of propositions in
predicate logic.

1. X ∨ Y, X ⊢ ¬Y             -- affirming the disjunct
2. X, Y ⊢ X ∧ Y              -- and introduction
3. X ∧ Y ⊢ X                 -- and elimination left
4. X ∧ Y ⊢ Y                 -- and elimination right
5. ¬¬X ⊢ X                   -- negation elimination 
6. ¬(X ∧ ¬X)                 -- no contradiction
7. X ⊢ X ∨ Y                 -- or introduction left
8. Y ⊢ X ∨ Y                 -- or introduction right
9. X → Y, ¬X ⊢ ¬ Y           -- denying the antecedent
10. X → Y, Y → X ⊢ X ↔ Y      -- iff introduction
11. X ↔ Y ⊢ X → Y            -- iff elimination left
12. X ↔ Y ⊢ Y → X            -- iff elimination right
13. X ∨ Y, X → Z, Y → Z ⊢ Z  -- or elimination
14. X → Y, Y ⊢ X             -- affirming the conclusion
15. X → Y, X ⊢ Y             -- arrow elimination
16. X → Y, Y → Z ⊢ X → Z     -- transitivity of → 
17. X → Y ⊢ Y → X            -- converse
18. X → Y ⊢ ¬Y → ¬X          -- contrapositive
19. ¬(X ∨ Y) ↔ ¬X ∧ ¬Y       -- DeMorgan #1 (¬ distributes over ∨)
20. ¬(X ∧ Y) ↔ ¬X ∨ ¬Y       -- Demorgan #2 (¬ distributes over ∧)
-/

/-
In what follows, we present the familiar inference 
rules above but now in the context of the more expressive
predicate logic of the Lean Prover tool. A big benefit 
is that "Lean" checks the syntax of our expressions.

We've also added inference rules for the quantifiers, ∀ and
∃, which of course are not relevant in propositional logic 
but that are essential in predicate logic (whether first- or
higher-order).
-/

