/- TEXT:
*******************
From Truth to Proof
*******************

In both propositional and first order predicate logic,
inference rules are defined in terms of *truth judgments*. 
For example, in our propositional logic, we defined the 
*and elimination left* rule as (⟦ P ∧ Q ⟧ i == tt) → 
⟦ P ⟧ i = tt. You can read it as saying, if we've judged
that P ∧ Q is true under some interpretation, i, then it 
must be that P is also true under that interpretation.

In the logic of Lean, by contrast, inference rules are
defined in terms of *proof* judgments. In Lean, if *P* 
is a proposition, then to express the idea that p is a 
proof of P, we write (p : P). We can also read this proof
judgement as a type judgment: that p is a value of type P. 
The and elimination left rule thus changes to the following:
TEXT. -/

-- QUOTE:
def and_elim_left_rule' := ∀ (P Q : Prop), P ∧ Q → P
-- QUOTE.

/- TEXT:
You can read the proposition as saying the following:
if P and Q are arbitrary propositions, then if you are
given a *proof* (value) of (type) P ∧ Q, then you can
derive a proof (value) of (type) P.

Written in the typical inference rule styles you will
find in the literature, we'd see something like this: 
*(P Q : Prop) (p : P) (q : P) ⊢ ⟨p,q⟩ : P ∧ Q*. 

In a textbook, it'd often be assumed or implicit that 
*P* and *Q* are propositions, in which case this rule
would be shortened to *P, Q ⊢ P ∧ Q*. 

Using Lean's *variables* declaration, we can achieve 
the same clarity with complete formality. 
TEXT. -/

-- QUOTE:
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
-- QUOTE.

/- TEXT: 
We can now assert the validity of this rule, and prove
it. Of course the proof in this case will be nothing 
but the application of Lean's version, and.elim_left.
TEXT. -/

-- QUOTE:
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
-- QUOTE.

/- TEXT:

Practice Example
----------------
Exercise: Define two propositions (types in Prop) with 
made up names, each having two proof constructors also
with made up names. Recall that we define types with an
*inductive* definition. Here's the exact definition of
the bool type, for example. 

inductive bool : Type
| tt 
| ff 

The big difference now is that we want to represent
logical propositions, so we will define types not in 
the universe, Type, but in Prop, the universe that all
logical propositions inhabit. Now it's easy as the next
example shows. We define two propositions, each with
two "proofs," and show that we can construct a proof
of the the conjunction of the two propositions.
TEXT. -/

-- QUOTE:

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
-- QUOTE.
