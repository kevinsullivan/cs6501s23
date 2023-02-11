

section pred_logic
variables X Y Z : Prop

def arrow_all_equiv   := (∀ (x : X), Y) ↔ (X → Y)




#check X → Y          -- Lean confirms this is a proposition
#check ∀ (x : X), Y   -- Lean understands this to say X → Y!



theorem all_imp_equal : (∀ (x : X), Y) = (X → Y) := rfl 


def arrow_elim        := (X → Y)        → X   → Y
def all_elim          := (∀ (x : X), Y) → X   → Y



variable Ball : Type            -- Ball is a type of object
variable isBlue : Ball → Prop



variables (b1 b2 : Ball)


#check isBlue                               -- a predicate
#check isBlue b1                            -- a proposition about b1
#check isBlue b2                            -- a proposition about b2
#check (∀ (x : Ball), isBlue x)             -- generalization
variable all_balls_blue : (∀ (x : Ball), isBlue x)   -- proof of it
#check all_balls_blue b1                    -- proof b1 is blue
#check all_balls_blue b2                    -- proof b2 is blue







def arrow_trans       := (X → Y) → (Y → Z) → (X → Z)

end pred_logic
