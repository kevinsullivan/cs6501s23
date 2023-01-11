section pred_logic

/-
Here are the logical fallacies we first met in propositional
logic, now presented in the richer context of constructive
logic. You might guess that it will be impossible to construct
proofs of these fallacies, and you would be correct.
-/

variables X Y Z : Prop

def converse          := (X → Y) → (Y → X)
def deny_antecedent   := (X → Y) → ¬X → ¬Y
def affirm_conclusion := (X → Y) → (Y → X)
def affirm_disjunct   := X ∨ Y → (X → ¬Y)

end pred_logic