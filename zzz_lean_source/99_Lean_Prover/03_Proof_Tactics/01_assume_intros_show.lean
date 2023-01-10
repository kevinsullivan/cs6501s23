/- *** assume and intro(s) *** -/

/-
Assume P, Q, and R are propositions in this 
variables (P Q R : Prop). This means they will
be "introduced/assumed" implicity as needed in
all definitions that follow. 
-/ 
variables (P Q R : Prop)

/-
The assume and intro(s) tactics work the same.
They implement ∀ and → introduction. That is,
if you need to prove ∀ (p : P), Q or P → Q, you
need to assume you're given a proof/value of P
and show that in that context you can derive a
proof/value of Q. Consider this example then 
read the discussion that follows. 
-/

example : P → Q :=
begin
/- 
Note: P, Q are already introduced as props.  
What remains to be proved is P → Q. We can
prove it using arrow introduction: assume P,
show Q (in the context of that assumption),
and finally conclude P → Q.
-/ 
assume p,
show Q,
_
/-
The show tactic does nothing here. It can
be used to select from among multiple goals,
or to change the form of the goal as long
as it means exactly the same thing as the
original goal. It's used to make our formal
proof scripts readable and self-documenting.

Of course we have no way to prove Q here. 
What the example shows is how to start to
prove any implication: assume P, show Q!
-/
end

example : ∀ (p : P), Q :=
begin
  /- 
  Note: What remains to be proved is P → Q
  What? Yeah! ∀ (p : P), Q means the same thing
  as P → Q, and that's how Lean prefers to print
  it! The intro keyword implements ∀ introduction.
  For stylistic purposes, specifiers might prefer
  to use intro(s) instead of assume. Your choice. 
  -/
  intro p,
  show Q,
  _
end 

/-
You can make multiple assumptions in one line
of proof script, using either assume or intros
(plural).
-/

-- using intros
example : ∀ (n m : ℕ), n + m = 0 :=
begin
  intros n m,
  _
end

-- using assume
example : ∀ (n m : ℕ), n + m = 0 :=
begin
  assume n m,
  _
end