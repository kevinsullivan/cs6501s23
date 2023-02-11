
section pred_logic
variables X Y Z : Prop

def iff_intro         := (X → Y) → (Y → X) → X ↔ Y


def iff_elim_left     := X ↔ Y → (X → Y)
def iff_elim_right    := X ↔ Y → (Y → X)


end pred_logic

