
-- Please briefly revisit especially prop_expr and pEval
import .A_05_prop_logic_properties
namespace cs6501


example : 
∀ (p q : prop_expr) (i : prop_var → bool),
  pEval (p ∧ q) i = pEval (q ∧ p) i :=
and_commutes  -- proof from last chapter



notation (name := pEval) ` ⟦ ` p ` ⟧ `  :=  pEval p


/-
We can declare a set of variables to be used across
multiple definitions within a section. 
-/
section prop_logic_axioms

-- Let p, q, r, and i be arbitrary expressions and an interpretation
variables (p q r : prop_expr) (i : prop_var → bool)

-- now we can write expressions with these variables without explicitly introducing them by ∀ 
-- we add prime marks just to avoid naming conflicts, the primes have no special meaning here
def and_commutes' := ⟦(p ∧ q)⟧ i = ⟦(q ∧ p)⟧ i 
def or_commutes' :=  ⟦(p ∧ q)⟧ i = ⟦(q ∧ p)⟧ i

/-
Comparing the types of our initial proof that and 
commutes with our new definition shows that they are
same if you understand that ∀-quantified variables
to be the same as function arguments. 
-/
#check and_commutes
#check and_commutes'

/-
Observe: We can *apply* these theorems
to particular objects to specalize the
generalized statement to the particular
objects.
-/

variables (a b : prop_expr)
#reduce and_commutes' p q i
#reduce and_commutes' a b i


-- re-doing proof with new notation
example : and_commutes' p q i := 
begin
-- expand definitions
unfold and_commutes',
unfold pEval bin_op_sem,
-- rest by case analysis as usual
sorry,
end 


def and_associative_axiom :=  ⟦(p ∧ q) ∧ r⟧ i = ⟦(p ∧ (q ∧ r))⟧ i
def or_associative_axiom :=   ⟦(p ∨ q) ∨ r⟧ i = ⟦(p ∨ (q ∨ r))⟧ i


def or_dist_and_axiom := ⟦p ∨ (q ∧ r)⟧ i = ⟦(p ∨ q) ∧ (p ∨ r)⟧ i
def and_dist_or_axiom := ⟦p ∧ (q ∨ r)⟧ i = ⟦(p ∧ q) ∨ (p ∧ r)⟧ i

-- Homework


def demorgan_not_over_and_axiom := ⟦¬(p ∧ q)⟧ i = ⟦¬p ∨ ¬q⟧ i
def demorgan_not_over_or_axiom :=  ⟦¬(p ∨ q)⟧ i = ⟦¬p ∧ ¬q⟧ i

-- Homework


def negation_elimination_axiom := ⟦¬¬p⟧ i = ⟦p⟧ i



def excluded_middle_axiom := ⟦p ∨ ¬p⟧ i = ⟦⊤⟧ i   -- or just tt



def no_contradiction_axiom := ⟦p ∧ ¬p⟧ i = ⟦⊥⟧ i   -- or just tt



def implication_axiom := ⟦(p => q)⟧ i = ⟦¬p ∨ q⟧ i  -- notation issue


example : implication_axiom a b i := 
begin
unfold implication_axiom pEval bin_op_sem un_op_sem,
cases ⟦ a ⟧ i,
cases ⟦ b ⟧ i, 
apply rfl,  -- Yay, now we can build a proof!!! 
apply rfl,
cases ⟦ b ⟧ i, 
apply rfl,
apply rfl,
-- = bnot ( ⟦ a ⟧ i) || ⟦ b ⟧ i
end







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

-- 11. (X ⊢ Y) ⊢ (X → Y)      -- a little complicated
-- 12. X → Y, X ⊢ Y           -- arrow elimination

-- 13. X → Y, Y → X ⊢ X ↔ Y    -- iff introduction
-- 14. X ↔ Y ⊢ X → Y          -- iff elimination left
-- 15. X ↔ Y ⊢ Y → X          -- iff elimination right

end prop_logic_axioms
end cs6501
