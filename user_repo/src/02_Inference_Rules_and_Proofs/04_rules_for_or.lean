



section pred_logic
variables X Y Z : Prop



def or_intro_left : Prop    := X → X ∨ Y
def or_intro_right : Prop   := Y → X ∨ Y
def or_elim : Prop          := (X ∨ Y) → (X → Z) → (Y → Z) → Z



end pred_logic