/- TEXT:
********
Theorems
********

As homework, reformulate each of axioms we proved for
propositional logic as its analog in Lean's predicate
logic, and then prove each proposition. 
TEXT. -/

-- QUOTE:

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
-- QUOTE.

/- TEXT:
Generating this answer required us to
solve two problems: formulate the axiom
in Lean, with propositions as types and
inference rules specified in terms of 
*proof* judgments (and other values).

Your homework, then, is, first, to 
formally define each of the axioms of 
propositional logic but generalized
to the logic of Lean, and, second 
and separately to produce proofs of
each axiom. 
TEXT. -/
