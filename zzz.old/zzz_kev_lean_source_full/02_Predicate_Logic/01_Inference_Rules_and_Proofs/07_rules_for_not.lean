section pred_logic

variables X Y Z : Prop

/- *** NOT *** -/


-- ¬ 
/-
With an understanding of "false" and its elimination rule, we
can now talk about the inference rules for negation. 
-/

/-
Recall that if P is any proposition, then (not P), generally 
written as ¬P, is also a proposition. when is ¬P true? It's
true in first-order logic if P is false. It's also true in
constructive logic when P is false, which is to say, *when 
there are no proofs of P*. 

Now here's the slightly tricky way that we show that there can
be no proof of P. We show (P → false). What this proposition
says is that "If there is a proof of P, then from it we can
derive an impossibility, so there must be no proof of P. This
is the rule of false introduction: prove P → false, conclude
¬P. ¬P is true iff P → false. Indeed, in our logic we simply
*define* ¬P to mean P → false.  
-/

/- 
Right click on not and click "go to definition" to see the
definition of (not P) and the definition of ¬P as a notation
for (not P).
-/

#check not 

/-
Examples
-/


example : 0 = 1 → false :=
begin
assume h,   -- assume 0 = 1; this can't happen, of course
cases h,    -- there's no way to prove 0 = 1, so NOT (0=1)
end 

/-
Here's exactly the same proposition but using ¬ notation
-/
example : ¬(0 = 1) :=
begin 
assume h,
cases h,

/-
Remember!  0 ≠ 1 means ¬(0 = 1) means 0 = 1 → false. You 
must remember that when you want to prove ¬P, that means 
you need to prove P → false: that a proof of P is an 
impossibility.  Remember this, because it tells you how
to prove ¬P. To show it, assume the premise, 0 = 1, then
show that this assumption gives rise to an impossibility
(a proof of false). 
-/
end

/- PROOF BY NEGATION 

What we've now seen is a crucial "proof strategy" often 
called "proof by negation."" To show ¬P (that P is false), 
we prove P → false. How? assume P is true and show that from 
this assumption you can derive a contradiction, something 
that cannot be, such as proof of false. 
-/

/-
HW #3 Exercise: state and prove the rule (the "theorem") 
of "no contradiction:" first in English and then in the
predicate logic of Lean. Or if you prefer, work it out 
in Lean and the write it in English. The formal statement
of the proposition is in the partially completed theorem 
below. 
-/

/-
English. Prove ¬(X ∧ ¬X), where X is any proposition.
This theorem states that it cannot be the case that 
both X and ¬X are true.

Proof by negation: Assume that (X ∧ ¬X) is true. By
use of and elimination deduce X and ¬X separately. 
But this is a contradiction, so the assumption must
have been false. Therefore ¬(X ∧ ¬X) is proved. QED.
-/

theorem no_contradiction : ¬(X ∧ ¬X) :=
begin
assume h,           -- where h proves (X ∧ ¬X)
cases h with x nx,  -- applies and elimination 
exact (nx x),       -- (nx x) is a proof of false
end


/- PROOF BY CONTRADICTION 

First, recall that in proof by negation, we prove ¬P by 
assuming that P is true, deriving an impossibility, and
then concluding ¬P.

Proof by contradiction is just a tad more complicated. In
this proof strategy we prove P (rather than ¬P) by assuming
¬P (rather than P) and showing that *this* assumption leads
to an impossibility, a contradiction. What that proves is 
that ¬P must be false, which is to say, ¬¬P. Finally, from
there, we conclude P using *negation elimination*. This rule
is simply this (recall that we introduced X as an arbitrary 
propostion above):
-/

def neg_elim          := ¬¬X → X

/-
As a silly but simple example, let's prove that 0 = 0 using
the strategy of proof by contradiction.

Goal: Prove 0 = 0.
Proof (by contradiction). Assume h: ¬(0 = 0). Recall that 
this means h is a proof of (0 = 0) → false. But 0 = 0 is
true, so there is a proof of it, let's call it pf. Now we
simply apply h to pf (arrow elimination) to derive a proof
of false. By ¬ introduction, this proves ¬¬(0 = 1). Finally
we apply negation elimination to deduce that (0 = 1) is true. 
-/


/-
In Lean, "by_contradiction" is the name of the negation 
elimination rule. Because it relies on a non-constructive
assumption, it's tucked away in a module called classical. 
We can use it by referring to classical.by_contradiction.
The @ sign here is a detail you can ignore for now. It
just tells Lean to report the rule as its' written where
it's defined.

-/
#check @classical.by_contradiction
-- ∀ {p : Prop}, (¬p → false) → p
-- in other words, ∀ (P : Prop), ¬(¬P) → P
-- Proof by contradiction is application of ¬ elimination!

-- Here's a formal proof
example : 0 = 0 :=
begin
apply classical.by_contradiction,
assume h,               -- assume ¬ 0 = 0
let k := eq.refl 0,     -- but we can have k a proof of 0 = 0
let f := h k,           -- that's an impossibility (here a proof of false)
apply false.elim f,     -- ex falso quodlibet! QED.
end


-- We can't prove negation elimination to be valid in constructive logic!
example : ∀ (P : Prop), ¬¬P → P :=
begin
assume P,
assume nnp,
-- stuck!!!
end

/-
But as a real wonder, it turns out that if you assume 
that the law of the excluded middle is valid, then that
is sufficient to make negation elimination valid again.
-/

/- 
The axiom of the excluded middle says that any and
every proposition has a Boolean truth value: it is
either true, or false, and there's nothing else it
could be. 

In constructive logic, by contrast, if you don't 
have either a proof of P or of ¬P, then you can't
build a proof of P ∨ ¬P. By contrast, in "classical"
logic for any proposition, P, you have have a proof
of P ∨ ¬P "for free," just by applying em to P.
-/

-- In Lean, classical.em is a proof of ∀ P, P ∨ ¬P.
#check @classical.em
-- em : ∀ (p : Prop), p ∨ ¬p

/-
The crucial point about the law of the excluded
middle is that (because it's a universal generalization)
you can *apply* it to any proposition, P, to get a "free" 
proof of P ∨ ¬P; *and on that you can do case analysis,*
with just two cases: in one case P is true because you
have a proof of it; and in the other case you have a 
proof of ¬P. As long as you can show that your goal
follows "in either case", you've proved your goal.
-/

/-
So let's see exactly how accepting the law of the 
excluded middle (em) suffices to prove the validity 
of negation elimination, ¬¬P → P. Remember that proof
by contradiction is used to prove P by assuming ¬P
and showing that that yeilds an impossibility, thus
proving ¬(¬P), from which, by negation elimination
you can deduce P, which was the original goal.

Here's the final secret. Read negation elimination
rule backwards. What is says is that if you want
to prove P, it will *suffice* to prove ¬¬P, for if
you do that, you just apply negation elimination
to prove P.

In other words. if your goal is P, and you apply
negation elimination, your new goal is to prove
¬¬P. Now recall that ¬¬P just means (¬P) → false.
To prove this, assume ¬P! And then show that this
assumption leads to a situation that can't happen,
and where therefore there is nothing else to be
considered. False elimination really means that
you can ignore the consequences of situations
that can never even happen in the first place.
-/

-- If we assume em, then negation elimination is valid
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

/-
Exercises: Prove that the following propositions are theorems
(that they have proofs). Express your proofs in English. For
extra credit, provide formal proofs in Lean. Hint: Working out
the proofs in Lean can be a big help to expressing them in 
English.
-/

-- prove that these propositions are 
def contrapostitive   := (X → Y) → (¬Y → ¬X)
def demorgan1         := ¬(X ∨ Y) ↔ ¬X ∧ ¬Y
def demorgan2         := ¬(X ∧ Y) ↔ ¬X ∨ ¬Y


/- EXTRA MATERIAL/CREDIT

It also turns out that if you assume that negation 
elimination, (¬¬P → P) is valid, then you can prove
that excluded middle is, too: (∀ (P : Prop), P ∨ ¬P). 

Indeed, in our logic, the two axioms are equivalent.
Here's a formal statement of that proposition, with
an extra credit opportunity for you to prove it in
both directions.
-/

theorem em_equiv_pbc : 
  ∀ (P : Prop), (P ∨ ¬P) ↔ (¬¬P → P) := 
begin
_         -- challenge problem, on your own
end

/-
Assume P is a proposition then see that you can
"apply iff.intro _ _") to construct a proof for
your overall goal. You're done, with you nidge:
you "borrowed" proofsfrom the future and now you
have to pay them back. You're thus left with two
remaining sub-goals. In this way, you provide a
complete proof but with some "blanks" that still
need to be filled in. Lean typechecks such proofs 
with holes and knows the types of proofs/values
needed for each one. These are the subgoals that
remain.

This is the vitally important computer science
"strategy" of top-down, structured, type-guided 
decomposition of a problem. You apply to a hard
problem by producing a complete solution pending
completion of remaining holes; then you apply
the same strategy to fill each hole; until you
fill holes with values that themselfes have no
remaining holes! Then you're done.

What's saddening, always a little at least, is
when you've expanded a whole tree of holes and
then filled in many only to find that you're
stuck. Yeah, that can make it hard to *find*
proofs. You must back up, undo some assumptions,
and then move forward ahead. This is called a
back-tracking search strategy. Mathematicians
*search* for proofs. Those who are especially
goodhave uncanny senses for unpromising paths
to avoid. 

Even so, the complete formalization of a proof
of the Four-Color Theorem took G.Gonthier six 
years to complete at Microsoft Research. Along
the way he had to build a significant formal
theory of a lot of the underlying mathematics,
e.g., in such areas as topology.

Main take-away message: when a proof of Q is
needed, we can often apply an inference rule
or theorem, to assumed arguments, to constrct
a proof of Q *even if we don't have values for
the arguments yet*. In this way, we build a
complete solution "modulo" remaining "proof
obligations," or "subgoals." This approach
is top-down, structured (read hierarchical), 
type-guided decomposition. It reduces a hard
problem to a complete solution in one step,
pending the satisfaction of zero or more 
remaining subproblems. If it's zero, QED; if
not, keep going, consider backtracking, etc. 
-/

end pred_logic