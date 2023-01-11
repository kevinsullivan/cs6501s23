/-
Let's construct a fully formal and certifiable correct proof of the 
commutativity of conjunction.
-/

-- theorem and_commutes : ∀ (P Q : Prop), P ∧ Q → Q ∧ P := _

theorem                           -- keyword: we're going to create a proof
and_commutes:                     -- this will be its name
∀ (P Q : Prop), P ∧ Q → Q ∧ P     -- the proposition/claim to be proved
:=                                -- bind the proof to the name, and_commutes
begin                             -- ⊢ ∀ (P Q : Prop), P ∧ Q → Q ∧ P
  assume P Q,                     -- P Q : Prop ⊢ P ∧ Q → Q ∧ P       (∀-intro)
  assume h : P ∧ Q,               -- P Q : Prop, h : P ∧ Q ⊢ Q ∧ P    (→ intro)
  let p : P := and.elim_left h,   -- P Q : Prop, h : P ∧ Q, p : P ⊢ Q ∧ P   (∧-elim-left)
  let q : Q := and.elim_right h,  -- P Q : Prop, h : P ∧ Q, p : P, q : Q ⊢ Q ∧ P  (right)
  apply and.intro q p,            -- QED (that means the claim has been proven)
end

/-
Theorem: Logical "and" is commutative.

Proof: Assume P and Q are arbitrary but specific propositions, 
and that we have proof of P ∧ Q. From this proof we can derive
proofs of P and of Q separately (using and elimination). Then 
we can combine these proofs in the opposite order to construct 
a proof of Q ∧ P.
-/

-- Here are two versions of a formal proof

theorem         -- a keyword saying we're going to construct a proof
or_commutes:   -- the name we'll give to the proof once it's accepted
∀ (P Q : Prop), P ∧ Q → Q ∨ P -- the proposition that's to be proved
:=              -- syntax for binding a name to a (proof) value
begin           -- and now, between begin/end, we build the proof 
/-
  intros P Q,
  assume h : P ∨ Q,
  apply or.elim h _ _,
  
  -- case where P ∨ Q is true because P is
  assume p : P,
  apply or.intro_right,
  exact p,

  -- case where P ∨ Q is true because Q is
  assume q : Q,
  apply or.intro_left,
  exact q,
-/
  -- In either case, we can prove that Q ∨ P is true. QED.
assume P Q h,
cases h with p q,      -- applies or.elim to h
exact or.inr p,
-- exact or.inl q,
end

example : 
  ∀ (P Q R S: Prop),
    R → P ∨ Q ∨ R ∨ S :=
begin
  intros P Q R S,
  assume r,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_left,
  assumption,
end

example : ∀ (P Q R S: Prop),
    Q → R → P ∨ Q ∨ R ∨ S := _

example : 
  ∀ (P Q R: Prop), 
    (P ∨ Q) ∧ R →
    (P ∧ R) ∨ (Q ∧ R) :=
begin
  intros P Q R h,
  cases h with pq r,
  cases pq with p q,
  apply or.intro_left,
  apply and.intro p r,
  apply or.intro_right,
  apply and.intro q r,
end 

/-

-/


example : 
  ∀ (P Q R S: Prop), 
    (P ∨ Q) ∧ (R ∨ S) →
    (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  intros P Q R S h,
  cases h,
  cases h_left with p q,
  cases h_right with r s,
  
  apply or.intro_left,
  apply and.intro p r,

  apply or.intro_right,
  apply or.intro_left,
  apply and.intro p s,

  cases h_right with r s,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_left,
  apply and.intro q r,

  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_right,
  apply and.intro q s,
end 

#print or_commutes