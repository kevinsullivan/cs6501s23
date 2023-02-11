


section pred_logic


variables X Y Z : Prop
def converse          := (X → Y) → (Y → X)
def deny_antecedent   := (X → Y) → ¬X → ¬Y
def affirm_conclusion := (X → Y) → (Y → X)
def affirm_disjunct   := X ∨ Y → (X → ¬Y)

end pred_logic