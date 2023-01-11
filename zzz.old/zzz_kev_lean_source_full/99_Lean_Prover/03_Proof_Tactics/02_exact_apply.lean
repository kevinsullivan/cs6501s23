/-
The "exact" and "apply" tactics construct proofs
of the current goal. 

The exact tactic is meant to be given a *complete* 
proof term, with no remaining holes (placeholders)
that remain to be filled in. 

The apply tactic will accept a complete proof term,
and so can be used anywhere "exact" is used, but it
is reall meant to accept proof terms with holes that
remain to be filled in with actual values. These 
holes are generally arguments that need to be provided
to some inference rule, or proof of an implication or
generalization, for it to construct a final, complete
proof. 

Let's see some simple examples. (We start by stating
that P Q and R should be treated as variables of type
Prop).
-/

variables P Q R : Prop  -- assume these are props


/-
Now recall the inference rule for ∧. 

(p : Q) (q : Q) ⊢ (pq : P ∧ Q) [and.intro]

In other words, and.intro is a procedure
that *takes* two arguments, here called p
and q, and *constructs* a proof of P ∧ Q. 
-/


-- an example using exact
example : P → Q → P ∧ Q :=
begin
  assume (p : P) (q :Q),
  exact (and.intro p q),
  -- QED!
end

-- an example using apply
example : P → Q → P ∧ Q :=
begin
  assume (p : P) (q :Q),
  apply (and.intro _ _),
  -- The _'s become subgoals
  exact p,
  exact q,
  -- This is top-down structured decomposition
end

-- you can leave out the _ _ by the way
example : P → Q → P ∧ Q :=
begin
  assume (p : P) (q :Q),
  apply (and.intro),      -- _ _ left out
  exact p,                -- now we fill holes 
  exact q,
end

-- You can even provide *some* arguments!

-- you can leave out the _ _ by the way
example : P → Q → P ∧ Q :=
begin
  assume (p : P) (q :Q),
  apply (and.intro _ q),      -- _ _ left out
  exact p,                -- now we fill holes 
end

example : P ↔ Q :=
begin
  apply iff.intro _ _,
end 