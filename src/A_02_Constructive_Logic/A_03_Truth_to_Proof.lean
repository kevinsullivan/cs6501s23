
def and_elim_left_rule' := ∀ (P Q : Prop), P ∧ Q → P


-- Let P, Q, and R be arbitrary propositions
variables (P Q R : Prop)

-- Now we can write the rule without the forall 
def and_elim_left_rule := P ∧ Q → P

/-
Lean doesn't treat the two versions exactly the 
same. The type of and_elim_left_rule is of course
just Prop, because it's a proposition. However,
because we've declared *P* and *Q* to be general
in the current environment, they are understood
as arguments, allowing and_elim_left_rule to be
*applied* to any two propositions as arguments
(say P, Q), yielding the specified proposition as
a result. 
-/
#reduce and_elim_left_rule'   -- just a proposition
#reduce and_elim_left_rule    -- function to proposition

#check and_elim_left_rule         -- Prop → Prop → Prop
#reduce and_elim_left_rule        -- A proposition
#reduce and_elim_left_rule P Q    -- Namely, P ∧ Q → P

#check and_elim_left_rule'       -- just Prop
#check and_elim_left_rule' P Q   -- Can't be applied

-- and_elim_left_rule applies to *any* propositions
variables (A B : Prop)
#check and_elim_left_rule A B
#reduce and_elim_left_rule A B


theorem and_elim_left_valid : and_elim_left_rule P Q :=
-- assume h is a proof of P → Q, show P
begin 
unfold and_elim_left_rule,
intro h, 
-- apply and.elim_left h
exact h.left,
end

-- The theorem now applies generally to any propositions

theorem and_elim_left_valid_2 : and_elim_left_rule A B :=
begin
apply and_elim_left_valid,
end



-- A proposition called KevinIsFromCville with two proofs
inductive KevinIsFromCville : Prop
| DL  -- driver's license
| EB  -- electric bill

-- Another similar proposition
inductive NickIsFromNewHampshire : Prop
| DL      -- driver's license
| EB      -- electric bill
| LFODLP  -- secret code

-- Because we can prove each one we can prove the conjunction
example : KevinIsFromCville ∧  NickIsFromNewHampshire :=
begin
apply and.intro _ _,
exact KevinIsFromCville.EB,
exact NickIsFromNewHampshire.LFODLP,
end

-- Similarly, from a proof of a conjunctions we can prove each
example : KevinIsFromCville ∧  NickIsFromNewHampshire → KevinIsFromCville :=
begin
assume h,
cases h,
assumption,
end
