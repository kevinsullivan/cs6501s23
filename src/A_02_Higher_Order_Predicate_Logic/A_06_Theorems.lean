

-- Let P, Q, and R be arbitrary propositions
variables P Q R : Prop

-- Let's reformulate and prove that ∧ is commutative
def and_commutes := P ∧ Q ↔ Q ∧ P

example : and_commutes P Q := 
begin
-- this solves it, modulo the holes
apply iff.intro _ _,

-- sub-proof: forward direction
assume h,
cases h,
apply and.intro _ _,
exact h_right,
exact h_left,

-- sub-proof: backward direction
assume h,
cases h with p q, -- use our names
exact and.intro q p,
end 

