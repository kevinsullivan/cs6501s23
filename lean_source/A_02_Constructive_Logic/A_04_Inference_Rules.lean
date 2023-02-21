/- TEXT:
***************
Inference Rules
***************

Next we'll see that most of the inference rules 
of propositional logic have analogues in constructive
predicate logic, provided to us by *mathlib*, Lean's
library of mathematical definitions. 

Your next major task is to know and understand these
inference rules. For each connective, learn its related
introduction (proof constructing) and elimination (proof
consuming) rules. Grasp the sense of each rule clerly.
And learn how to to compose them, e.g., in proof scripts, 
to produce proofs of more complex propositions. 

This new inference rule is just an "upgraded"
version of the and-elimination-left inference rule from 
from the last chapter. The major task in the rest of this
chapter is to "lift" your established understanding of all
of the inference rules of propositional logic to the level
of higher-order constructive logic. Along the way we'll see
a few places where the "classical" rules don't work.
TEXT. -/

/- TEXT: 
We now go through each rule from propositional logic and 
give its analog in the predicate logic of the Lean prover.

true (⊤)
--------

In propositional logic, we had the rule that ⊤, always 
evaluates to true (tt in Lean). The definition said this:
*true_intro_rule := ⟦ ⊤ ⟧ i = tt*.

In Lean, by contrast, there is a proposition, *true*, that 
has proof, called *intro*. We write *true.intro* to refer
to it in its namespace. 
TEXT. -/

-- QUOTE:
#check true                   -- a proposition
example : true := true.intro  -- a proof of it
-- QUOTE.

/- TEXT:
Now we'll see exactly how the proposition, true, with
true.intro as a proof, how it is all defined. It's simple.
Propositions are types, so true is a type, but one that
inhabits Prop; and it has one constant constructor and
that's the one and only proof, *intro*.That's it!

inductive true : Prop
| intro : true

Sadly, a proof of true is pretty useless. A value of this type
doesn't even provide one bit of information, as a Boolean value
would. There's no interesting elimination rule for true.
TEXT. -/


/- TEXT:

false
-----

In propositional logic, we had the propositional expression
(prop_expr), ⊥, for *false*. In Lean, by contrast, *false* is 
a *proposition*, which is to say, a type, called *false*. 
Because we want this proposition never to be true, we define
it as a type with no values/proofs at all--as an uninhabited
type. 

inductive false : Prop

There is no way ever to produce a proof of *false* because 
the type has no value constructors. There is no introduction 
rule false. 

In propositional logic, the false elimination rule said that
if an expression evaluates to ff, then it follows (implication)
that any other expression evaluates to tt. The rule in Lean is
called false.elim. It says that from a proof of false, a proof
(or value) of *any* type in any type universe can be produced:
not only proofs of other propositions but values of any types.
TEXT. -/

-- QUOTE:
#check false
#check @false.elim  -- false.elim : Π {C : Sort u_1}, false → C

-- explicit application of Lean's false.elim rule
example : false → 0 = 1 := 
begin 
assume f, 
exact false.elim f,       -- So what is C (_)? It's the goal, 0 = 1.
-- exact @false.elim _ f,    -- Note that C is an implicit argument!
end

/- 
We can also do case analysis on f. We will get
one case for each possible form of proof, f. As
there are no proofs of f, there are no cases at
all, and the proof is completed. 
-/
example : false → 0 = 1 := 
begin 
assume f, 
cases f, 
end

/-
False eliminations works for "return types" in any
type universe. When the argument and return types 
are both in Prop, one has an ordinary implication.  
-/
example : false → nat :=
begin
assume f,
cases f,
-- contradiction,  -- this tactic works here, too
end
-- QUOTE.

/- TEXT:

and ∧ 
-----

From propositional logic we had three inference rules defining
the meaning of *and*, one introduction and two elimination rules.
These rules re-appear in both first-order predicate logic and in
the higher-order logic of Lean, but now in a much richer logic.
In this chapter we'll see how this is done, using *and* as an 
easy example. 

- and_intro_rule := ⟦ X ⟧ i = tt → ⟦ Y ⟧ i = tt → ⟦(X ∧ Y)⟧ i = tt 
- and_elim_left_rule := (⟦(X ∧ Y)⟧ i = tt) → (⟦X⟧ i = tt)
- and_elim_right_rule := (⟦(X ∧ Y)⟧ i = tt) → (⟦Y⟧ i = tt)

Proposition Builders
~~~~~~~~~~~~~~~~~~~~

A key idea in Lean's definitions is that *and* is a *polymorphic* 
data type. That is to say, its akin to a function takes any two 
propositions (types in Prop) as arguments and yields a new Type.
This new type encodes the proposition that is the conjunction of
the given proposition arguments. Let's see how *and* is defined.
TEXT. -/

namespace hidden
-- QUOTE: 
structure and (A B : Prop) : Prop :=
intro :: (left : A) (right : B)
-- QUOTE.
end hidden

/- TEXT: 
The *structure* keyword is shorthand for *inductive* and can be 
used (only) when a type has just one constructor. The name of the
constructor here is *intro*. It takes two arguments, *left*, a 
proof (value) of (type) *A*, and *right*, a proof of *B*. 

A benefit of using the *structure* keyword is that Lean generates
field access functions with the given field names. For example, if
*(h : A ∧ B)*, then *(h.left : A)* and *(h.right : B)*.  

Introduction: Proof Constructors
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The second key idea is that the constructors of a logical type 
define what terms count as proofs, i.e., values of the type. 

In the case of a conjunction, there is just one constructor,
namely *intro,* takes two proof values as arguments and yielding
a proof of the conjunction of the propositions that they prove.  

Note: It's important to distinguish clearly between *and* and 
*intro* in your mind. The *and* connective (∧) is a proposition
builder, a type builder. It takes two *propositions* (types),
*(A B : Prop)* as its arguments and yields a new proposition 
(type) as a result, namely *(and A B),* also written as *A ∧ B*. 

On the other hand, *and.intro* is a *proof/value constructor.* 
It takes two *proof values, (a : A)* and *(b : B)* as arguments,
and yields a new proof/value/term, *⟨ a, b ⟩ : A ∧ B*. There is
no other way to construct a proof of a conjunction, *A ∧ B,* than
to use this constructor.

Elimination: Case Analysis
~~~~~~~~~~~~~~~~~~~~~~~~~~

Now that we've seen how to (1) construct a conjunction from two
given propositions, and (2) construct a proof of one, we turn to
the question, what can we *do* with such a proof if we have one.

The answer, in general, is that we can analyze how it could have
been built, with an aim to show that a given proof goal follows
in every case. If we can show that, then we've proved it always 
holds. 

An already familiar example is our earlier case analysis of values 
of type bool. When we do case analysis on an arbitrary bool value, 
we have to consider the two ways (constructors) that a bool can be
constructed: using the *tt* constructor or the *ff* constructor. A
proof by case analysis on a bool, b, thus requires two sub-proofs: 
one that shows a given goal follows if *b* is *tt* and another that
shows it follows if *b* is *ff*.  
TEXT. -/

-- QUOTE:
example (b : bool) :  bnot (bnot b) = b :=
begin
cases b,              -- NB: one case per constructor
repeat { apply rfl }, -- prove goal *in each case*
-- QED.               -- thus proving it in *all* cases
end
-- QUOTE.

/- TEXT:
Turning to a proof of a conjunction, *A ∧ B*, only two
small details change. First, there *and* has just one
constructor. So when we do case analysis, we'll get only
one case to consider. Second, the constructor now takes
two arguments, rather than zero as with tt and ff. So,
in that one case, we'll be entitled to assume that the
two proof arguments must have been given. These will be
the *left* and *right* proofs of *A* and *B* separately. 
TEXT. -/

-- QUOTE:
-- Case analysis on *proof* values 
example (X Y: Prop) : X ∧ Y → X := 
begin
assume h,           -- a proof we can *use*
cases h with x y,   -- analyze each possible case
exact x,            -- also known as destructuring
end

-- We can even use "case analysis" programming notation!
example (X Y: Prop) : X ∧ Y → X
| (and.intro a b) := a
-- QUOTE.



/- TEXT:
or ∨ 
----

- def or_intro_left_rule := (⟦X⟧ i = tt) → (⟦(X ∨ Y)⟧ i = tt) 
- def or_intro_right_rule := (⟦Y⟧ i = tt) → (⟦(X ∨ Y)⟧ i = tt) 
- def or_elim_rule :=   (⟦(X ∨ Y)⟧ i = tt) → (⟦(X => Z)⟧ i = tt) → (⟦(Y => Z)⟧ i = tt) → (⟦(Z)⟧ i = tt)

Just as with ∧, the ∨ connective in Lean is represented as
a logical type, polymorphic in two propositional arguments. 
TEXT. -/

namespace hidden
-- QUOTE:
inductive or (A B : Prop) : Prop
| inl (h : A) : or
| inr (h : B) : or
end hidden
-- QUOTE.

/- TEXT:
But whereas the intended meaning of ∧ is that each of two 
given propositions has a proof, the intended meaning of ∨ 
is that *at least one of* the propositions has a proof. This 
difference shows up in how proofs of disjunctions are created
and used. 

Introduction Rules
~~~~~~~~~~~~~~~~~~

We now have two constructors. The first, *or.inl*, constructs 
a proof of *A ∨ B* from a proof, (a : A). The second, *or.inr*, 
constructs a proof of *A ∨ B* from a proof of *B*. 
TEXT. -/

-- QUOTE:
-- Example using a lambda expression. Be sure you understand it. 
example (A B : Prop) : A → A ∨ B := fun (a : A), or.inl a
/-
Ok, you might have notice that I've been declaring some named
arguments to the left of the : rather than giving them names
with ∀ bindings to the right. Yes, that's a thing you can do. 
Also note that we *do* bind a name, *a*m to the assumed proof
of *A*, which we then use to build a proof of *A ∨ B*. That's
all there is to it.
-/
-- QUOTE.

/- TEXT:
Elimination Rules
~~~~~~~~~~~~~~~~~

How do we use a proof of a conjunction, *A ∨ B*? In general,
what you'll want to show is that if you have a proof, h, of 
*A ∨ B*  then you can obtain a proof of a goal proposition, 
let's call it C. 

The proof is constructed by case analysis on h. As *(h : A ∨ B)*
(read that as *h is a proof of A ∨ B*), there are two cases that
we have to consider: *h* could be *or.inl a*, where *(a : A)*, or
*h* could be *or.inr b*, where *(b : B).*  

But that's not yet enough to prove *C*. In addition, we'll need 
proofs that *A → C* and *B → C*. In other words, to show that 
*A ∨ B → C*, we need to show that that true *in either case* in
a case analysis of a proof of *A ∨ B*. The elimination rule for 
∨ is thus akin to what we saw in propositional logic. 
TEXT. -/ 

-- QUOTE:
-- or.elim : ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-- deduce c from proofs of a ∨ b, a → c, and b → c, 
#check @or.elim 

example (P Q R : Prop) : P ∨ Q → (P → R) → (Q → R) → R
| (or.inl p) pr qr := pr p
| (or.inr q) pr qr := qr q

-- QUOTE.

/- TEXT:
Examples
~~~~~~~~
TEXT. -/

-- QUOTE:
example : ∀ P Q, P ∨ Q → Q ∨ P :=
begin
assume P Q h,
cases h with p q,
exact or.inr p,
exact or.inl q,
end


example : ∀ P Q R, P ∨ (Q ∨ R) → (P ∨ Q) ∨ R :=
begin
assume P Q R h,
cases h with p qr,
left; left; assumption,
cases qr with q r,
left; exact or.inr q,
right; assumption,
end
-- QUOTE.


/- TEXT:
not (¬)
-------
TEXT. -/

-- QUOTE:
-- ¬¬X ⊢ X                 -- negation elimination
-- X → ⊥ ⊢ ¬X             -- negation introduction
-- QUOTE.

/- TEXT:
Introduction
~~~~~~~~~~~~

We saw in propositional logic that if *X → false* then
*X* must be false. That's easy to see: *true → false* is
false, so *X* can't be *true*. On the other hand, *false 
→ false* is true. *X* can only be *false*. Now, saying *X
is false* in propositional logic is equivalent to saying 
¬X is true, giving us our constructive ¬ introduction rule:
X → ⊥ ⊢ ¬X. This is the rule of ¬ introduction: to prove
*¬X* it will suffice to prove *X → false*.

The same idea reappears in the constructive logic of Lean. 
In fact, Lean simply *defines* *¬X* to mean *X → false.* 
TEXT. -/

-- QUOTE:
-- def not (a : Prop) := a → false
-- prefix `¬`:40 := not
#check not
-- QUOTE.

example : ¬ 0 = 1 :=
begin
show 0 = 1 → false,
assume h,
contradiction,
end

/- TEXT:
Let's think about what *a → false* means, where *a* is any
proposition. In Lean, a proof of an implication is a function,
namely one that would turn *any* proof of *a* into a proof of
false. So, *if there were* a proof of *a* then one could have
a proof of *false.* That can't happen because there is no proof
of false. So there must be no proof of *a*. Therefore *a* is
false, and we can write that as *¬a*. 

To prove a proposition, *¬a*, we thus just have to prove that
*a → false*. To do this, we assume we have a proof of *a* and
show that that leads to an impossibility, which shows that the
assumption was wrong, thus *¬a* must be true. You can pronounce
*¬a* as *not a* or *a is false*, but it can also help to think 
of it as saying *there provably can be no proof of a.*  
TEXT. -/

-- QUOTE:
example : 0 = 1 → false :=
begin
assume h,
cases h,
end 

example : ¬ 0 = 1 :=
begin
assume h,
cases h,
end 

example : 0 ≠ 1 :=
begin
assume h,
cases h,
end 
-- QUOTE.

/- TEXT:
Elimination
~~~~~~~~~~~

In propositional logic, we have the rule of (double) negation
elimination: *¬¬X → X*. An easy way to think about this is that
two negations cancel out: negation is an involution. As we'll
now see, this rule is also defines proof by contradiction. 

To see that, one can read the rule as saying that to prove *X*
it will suffice to assume *¬X* and show that that leads to a 
a contradiction, thus proving that *¬X* is false, thus *¬¬X*.
From there in classical logic it's just a final step to *X*.  

Is this inference rule valid in Lean? Let's try to prove that
it is. Our goal is to prove ∀ X, ¬¬X → X. We first rewrite the
inner *¬X* on the left of the → as *(X → false)*. *¬¬X* becomes 
*¬(X → false)*. Rewriting again gives *(X → false) → false.*
Our goal, then, is to prove ((X → false) → false) → X. We get
a start by assuming (h : (X → false) → false), but then find 
that from *h* there's no way to squeeze out a proof of *X*. 
TEXT. -/

-- QUOTE:
example : ∀ (X : Prop), ¬¬X → X :=
begin
assume X h,
-- can't do case analysis on a function
cases h,
-- we're stuck with nowhere left to go!
end
-- QUOTE.

/- TEXT:
What we've found then is that (double) negation elimination, 
and thus proof by contradiction, is not valid in Lean (or in
similar constructive logic proof assistants). This shows that
in Lean a proposition, *X*, being proved *not false* (*¬¬X*) 
does not imply that *X* is true. From a proof of the former we
can't obtain a proof of the latter. From a proof that *¬X is 
false* we have no way to derive a proof of *X*.  

Constructive vs. Classical
~~~~~~~~~~~~~~~~~~~~~~~~~~

In constructive logic, a proposition can thus be provably true 
(by a proof), it can be provably false (by a proof that there is 
no proof of it), or it can be provably not false, which is to
say that there must exist a proof, but where one cannot be
constructed from the given premise alone.

We'll see the the same constructivity requirement again when we
discuss proofs of existence. In a nutshell, a constructive proof
exhibits a specific "witness" to show that one does exist. To be
constructive means that a proof of existence requires an actual
witness. 

With respect to negation elimination, it's not enough to know
that there's an unspecified proof of *X* "out there." To know
that *X* is true/valid, one has to *exhibit* such a proof: to
have one in hand, that can actually be inspected and verified.

Consider *em* again. Given any proposition, *X*, *(em X)* is 
a proof of *X ∨ ¬X*. Now consider the introduction rules for
∨ in constructive logic: to construct a proof of *X* you have
to have either a proof of *X* or a proof of *¬X* in hand. The
*em* axiom gives you a proof of *X ∨ ¬X* without requiring a
proof of either disjunction. It's thus non-constructive. 

Classical logic and mathematics do not adopt the constraint
of constructivity, and consequently there are theorems that
can be proved in classical mathematics but not in constructive
mathematics. Again, it's easy to turn Lean classical simply
by opening the classical namespace (the accepted signal that
one will admit classical reasoning) and using *em* in your
proofs. 
TEXT. -/


-- QUOTE:
-- A proof of 0 = 0 by contradition 
example : 0 = 0 :=
begin
by_contradiction, -- applies ¬¬P → P
have eq0 := eq.refl 0,
contradiction,
end
-- QUOTE.


/- TEXT: 
Excluded Middle
~~~~~~~~~~~~~~~
We've seen that in *constructive* logic, knowing that it's 
false that there's no proof is not the same as, and is weaker
than, actually having a proof. Knowing that a proposition is
not false is not the same as actually having a proof in hand.
What makes constructive logic constructive is that a proof is
required to judge a proposition as being true.

In classical predicate and propositional logic, by contrast,
negation elimination is an axiom. To prove a proposition, *X*,
by contradiction, one assumes *¬X*, shows that from that one 
can derive a contradiction, thus proving *¬¬X*, and from there
(here it comes) by negation elimination one finally concludes 
*X*, thereby satisfying the original goal.

In summary, negation elimination is not an axiom in constructive
logic, so any proof that relies on *∀ X, ¬¬X → X* gets blocked at
this point. The reason it's not an axiom is that it would make 
the logic non-constructive: while a proof that X is not false 
might suggest that there exists a proof of X, it does not give 
you such a proof, which is what constructive logic requires. 

In constructive logic there are not just two truth states 
for any proposition. We've seen that we can know that a 
proposition is true (by having a proof of it), know that 
it is false (by having a proof it entails a contradiction),
and know that it's not false but without having constructed
a proof that it's true. We can know that something is not
false without having a proof of it, and without a proof we
can't judge it to be true, either. 

In classical logic, the *axiom ("law") of the excluded middle*
rules out this middle possibility, declaring as an assumption
that for any given proposition, P, there is a proof of P ∨ ¬P.

This axiom then enables proof by contradiction. That's an easy
proof. We need to prove that if *P ∨ ¬ P* then *¬¬P → P*. The
proof is by case analysis on an assumped proof of *P ∨ ¬ P*.
In the first case, we assume a proof of P, so the implication
is true trivially. In the case where we have a proof of ¬P, we
have a contradiction between ¬P and ¬¬P, and so this case can't
actually arise and needn't be considered any further.

In Lean, you can declare anything you want to be an additional
axiom. If you're careless, you will make the logic inconsistent
and thus useless. For example, don't assume *true ↔ false*. On
the other hand, you may add any axiom that is independent of the
given ones and you'll still have a consistent logic in which
propositions that lack proofs in constructive logic now have
proofs. 

The law of the excluded middle, *∀ P, P ∨ ¬P* is declared as an
*axiom* in the *classical* namespace, where *classical.em* (or
just *em* if you *open classical*) is assumed to be a proof of
*em : ∀ P, P ∨ ¬P*.

Now the key to understanding the power of excluded middle is 
that it allows you to do case analysis on any *proposition* in
our otherwise constructive logic. How's that? Assume *X* is an
arbitrary proposition. Then *(em X)* is a proof of X ∨ ¬X. 

Note that *em*, being universally quantified is essentially 
a function. It can be *applied* to yield a specific instance 
of the general rule. Ok, so what can we do with a "free proof"
of *X ∨ ¬X*? Case analysis! There will be just two cases. In
the first case, we'd have a proof of *X*. In the second, we'd
have a proof of *¬X*. And those are the only cases that need
to be considered.  

Examples
~~~~~~~~
TEXT. -/

-- QUOTE:
#check@ classical.em 

theorem foo : ∀ P, (P ∨ ¬ P) → (¬¬P → P) :=
begin
assume P,
assume em,
assume notNotP,
cases em,
-- case 1
assumption,
contradiction,
end

example : 0 = 0 :=
begin
by_contradiction,
have zez := eq.refl 0,
contradiction, 
end

theorem demorgan1 : ∀ P Q, ¬(P ∧ Q) ↔ ¬P ∨ ¬ Q :=
begin
assume P Q,
split,

-- FORWARD
assume h,
have ponp := classical.em P,
have qonq := classical.em Q,

cases ponp with p np,
cases qonq with q nq,
have pandq := and.intro p q,
contradiction,
apply or.inr nq,
apply or.inl np,

-- BACKWARDS

assume h,


have ponp := classical.em P,
have qonq := classical.em Q,
cases ponp with p np,
cases qonq with q nq,

cases h,
contradiction,
contradiction,

-- FINISH THIS PROOF
-- IS BACKWARDS PROVABLE WITHOUT em?

end

-- PROVE THE SECOND DEMORGAN RULE
-- QUOTE.


/-
Exercise
~~~~~~~~

- Give a formal proof of the claim that excluded middle implies proof by contradiction.
- Determine whether, and if so prove, that the two statements are equivalent: excluded middle and proof by contradiction.
- Try to Prove each of DeMorgan's laws in Lean to identify the non-constructive ones
- Finish the proofs of DeMorgan's laws using the axiom of the excluded middle *(em)*.

Coming Soon
-----------
TEXT. -/


-- QUOTE:
/-
-- formalize the rest
-- 11. (X ⊢ Y) ⊢ (X → Y)      -- arrow introduction
-- 12. X → Y, X ⊢ Y           -- arrow elimination
-- 13. X → Y, Y → X ⊢ X ↔ Y   -- iff introduction
-- 14. X ↔ Y ⊢ X → Y          -- iff elimination left
-- 15. X ↔ Y ⊢ Y → X          -- iff elimination right
-/
-- QUOTE.