

section pred_logic
variables X Y Z : Prop





#check not 


section pred_logic
variables X Y Z : Prop

example : 0 = 1 → false :=
begin
assume h,   -- assume 0 = 1; this can't happen, of course
cases h,    -- there's no way to prove 0 = 1, so NOT (0=1)
end 



example : ¬(0 = 1) :=
begin 
assume h,
cases h,
end






theorem no_contradiction : ¬(X ∧ ¬X) :=
begin
assume h,           -- where h proves (X ∧ ¬X)
cases h with x nx,  -- applies and elimination 
exact (nx x),       -- (nx x) is a proof of false
end


def neg_elim          := ¬¬X → X



#check @classical.by_contradiction
-- ∀ {p : Prop}, (¬p → false) → p
-- in other words, ∀ (P : Prop), ¬(¬P) → P
-- Proof by contradiction is application of ¬ elimination!

-- TEXT:
Here's a formal proof
-- TEXT. 

example : 0 = 0 :=
begin
apply classical.by_contradiction,
assume h,               -- assume ¬ 0 = 0
let k := eq.refl 0,     -- but we can have k a proof of 0 = 0
let f := h k,           -- that's an impossibility (here a proof of false)
apply false.elim f,     -- ex falso quodlibet! QED.
end


example : ∀ (P : Prop), ¬¬P → P :=
begin
assume P,
assume nnp,
-- stuck!!!
end





#check @classical.em
-- em : ∀ (p : Prop), p ∨ ¬p





example : 
  ∀ (P : Prop),   -- for any proposition P
    (P ∨ ¬P) →    -- ***if we assume em is valid**
    (¬¬P → P)     -- ***then neg elim is valid***
  := 
begin
assume P,
assume em_P,
assume nnp,
cases em_P with p np,
-- case P
exact p,
-- "assumption" also works heew
-- case ¬P
apply false.elim (nnp np)
-- "contradiction" also works here
end


def contrapostitive   := (X → Y) → (¬Y → ¬X)
def demorgan1         := ¬(X ∨ Y) ↔ ¬X ∧ ¬Y
def demorgan2         := ¬(X ∧ Y) ↔ ¬X ∨ ¬Y


theorem em_equiv_pbc : 
  ∀ (P : Prop), (P ∨ ¬P) ↔ (¬¬P → P) := 
begin
_         -- challenge problem, on your own
end


end pred_logic