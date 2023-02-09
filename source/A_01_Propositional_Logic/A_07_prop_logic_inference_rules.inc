
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
truth. We do for propositional logic, but not predicate 
logic. Learning the basic inference rules of the logic
is thus essential for reasoning about the truth of given 
propositions expressed in predicate logic.


.. code-block:: lean

  import .A_06_prop_logic_algebraic_axioms 
  namespace cs6501

Inference Rules
---------------

Key idea: These are rules for reasoning about evidence.
What *evidence* do you need to derive a given conclusion?
These are the "introduction" rules. From a given piece of
evidence (and possibly with additional evidence) what new
forms of evidence can you derive? These are "elimination"
rules of the logic.

.. code-block:: lean

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
  


.. code-block:: lean

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

Practice
--------
In the style of the preceding examples, formally state,
name, and prove that each of the remaining inference are
also valid in our logic. Identify any rules that fail to be
provable in the presence of the bug we injected in bimp.
You can do this by completing the proofs and seeing how
they break when bugs are added to our definitions.

.. code-block:: lean

  -- Write your formal propositions and proofs here: 
  
  
  
  end cs6501

