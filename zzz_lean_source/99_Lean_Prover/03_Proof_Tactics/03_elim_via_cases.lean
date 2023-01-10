/-
The cases tactic applies the elimination
rules to a term, appropriate to it's type.

For example, if h is a proof of P ∧ Q, the
cases tactic will "eliminate" h to a proof
of p and proof of q; and that will be the
only case. Why? Because there's only one
way that the proof, h, could have been 
constructed, namely by the application of
and.intro to two arguments, a proof of P
and a proof of Q. 
-/

variables P Q R : Prop

/-
You *could* apply the elimination rules
"manually."
-/
example : P ∧ Q → P :=
begin
assume h,
let p : P := and.elim_left h,
exact p,
end

/-
Or you could just use the cases tactic
-/
example : P ∧ Q → P :=
begin
assume h,
cases h,
exact h_left,
end

/-
If you don't specify names for the 
results of the elimination, Lean will
make up names for you. It's better to
provide more meaningful names. It can
make a big difference in being able 
to think about what you've got. 
-/
example : P ∧ Q → P :=
begin
assume h,
cases h with p q, -- *with p q*
exact p,
end

/-
Now suppose you've got a proof of a type
for which there are two introduction rules.
There are now *two ways* that an assumed
proof could have been constructed. What you
generally want to know is that no matter
how the proof was constructive, the goal
remains true. To prove that, you need to
consider each *case*. 

Consider a proof of P ∨ Q. There are two
introduction rules: or.intro_left Q p and
or.intro_right P q. Note that if Lean is
able to infer the P and Q arguments, you
can use the simpler or.inl p and or.inr q
constructors. 
-/

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
assume h,
cases h with p q,
/-
What remain are two subgoals, one
for each case. If the proof, h, of 
P ∨ Q was constructed using or.inl,
then you need to show that given P,
R follows (basically P → R); and if
P ∨ Q was proven using or.inr q, you
need to complete the proof of Q → R.
(Given the assumed proof of Q, show
that R is true by provind a proof of
it.)
-/
end

/-
If we want to reason "classically"
rather than constructively, then we
can use the classical.em rule to
convert and proposition, P, into a
proof of P ∨ ¬P, *on which we can
then do case analysis*.
-/

#check @classical.em P

example : ¬¬P → P :=
begin
assume nnp,
cases (classical.em P) with p np, -- here!
-- make sure you can finish this proof!
exact p,
contradiction,
end

/-
How is a proof of P ↔ Q constructed? It's by
applying iff.intro to a proof of P → Q and to
a proof of Q → P. That's the only way to do
it. When we apply case analysis to a proof of
P ↔ Q we should thus expect one case, where
iff.intro was applied to two assumed argments
of the right types. That's just what we get.
-/

example : (P ↔ Q) → (Q → P) :=
begin
assume h,
cases h with pq qp,
assumption, -- uses proof in context
end


/-
As an aside, we can even do case analysis
on data values. The bool type, for example,
has two values.
-/

def my_not : bool → bool :=
begin
assume b,
cases b,
exact tt, -- in case b = tt, return ff
exact ff, -- in case b = ff, return tt
end

#eval (my_not tt)
#eval (my_not ff)

-- Whoa: we defined a function by cases! 

/-
Finally, case analysis works only on data
values, including proof values. It can't
be applied to functions. In the following
example, we assume we have a function that
takes a nat and returns a nat, along with
a nat. We'll first show how you can "prove
this type" by giving a particular function
value of this type; then we'll get to the
main point, which is to show that you will
get an error if you try to do case analysis
on the function argument. 
-/

def app_func : (ℕ → ℕ) → ℕ → ℕ :=
begin
assume f n,
exact (f n),
end

#eval

/-
What you have just proved is that if
f takes and returns a nat, and n is
a nat, then f applied to n is a nat.
What happens if we try "cases f"? It's
a no-go.
-/


example : (ℕ → ℕ) → ℕ → ℕ :=
begin
assume f n,
cases f,
/-
Error: "cases tactic failed, it is not 
applicable to the given hypothesis." You
can't do case analysis on a function, or
on a proof of an implication or universal
generalization, because these things are
basically functions.
-/

example : (P → Q) → P → Q :=
begin
assume i p,
exact (i p),
end

example : (P → Q) → P → Q :=
begin
assume i p,
cases i,      -- Nope
end

/-
Similarly you can't do case analysis
on a data *type* (such as bool) or on
a proposition (a logical *type*). These
things aren't data values, so "cases"
does not work. Independent of Lean, 
you can't do "case analysis" on things
of these kind in predicate logic.  
-/
