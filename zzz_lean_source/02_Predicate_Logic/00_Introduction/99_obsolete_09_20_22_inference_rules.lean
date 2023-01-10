/-
ATTENTION: This file got long and is now obsolete. 
Please see it broken into individual sections in the
Inference_Rules directory. We'll leave the original 
content in place below for reference in case you need
to look back.
-/

/-
As a reminder, here are the inference rules (and a few
"logical fallacies" that you tested for validity in the
setting of propositional logic, where the variables are
all Boolean, and where logical connectives correspond to
Boolean operations, such as &&, ||, and ! (C, C++, etc.) 

1. X ∨ Y, X ⊢ ¬Y             -- affirming the disjunct
2. X, Y ⊢ X ∧ Y              -- and introduction
3. X ∧ Y ⊢ X                 -- and elimination left
4. X ∧ Y ⊢ Y                 -- and elimination right
5. ¬¬X ⊢ X                   -- negation elimination 
6. ¬(X ∧ ¬X)                 -- no contradiction
7. X ⊢ X ∨ Y                 -- or introduction left
8. Y ⊢ X ∨ Y                 -- or introduction right
9. X → Y, ¬X ⊢ ¬ Y           -- denying the antecedent
10. X → Y, Y → X ⊢ X ↔ Y      -- iff introduction
11. X ↔ Y ⊢ X → Y            -- iff elimination left
12. X ↔ Y ⊢ Y → X            -- iff elimination right
13. X ∨ Y, X → Z, Y → Z ⊢ Z  -- or elimination
14. X → Y, Y ⊢ X             -- affirming the conclusion
15. X → Y, X ⊢ Y             -- arrow elimination
16. X → Y, Y → Z ⊢ X → Z     -- transitivity of → 
17. X → Y ⊢ Y → X            -- converse
18. X → Y ⊢ ¬Y → ¬X          -- contrapositive
19. ¬(X ∨ Y) ↔ ¬X ∧ ¬Y       -- DeMorgan #1 (¬ distributes over ∨)
20. ¬(X ∧ Y) ↔ ¬X ∨ ¬Y       -- Demorgan #2 (¬ distributes over ∧)
-/

/-
Here we present the familiar inference rules above but 
now in the context of the more expressive, higher-order
predicate logic of the Lean Prover tool. A big benefit 
is that "Lean" checks the syntax of our expressions.

Note that we've reordered the inference rules you've already
seen, putting all of the inference rules related to any given
connective or quantifier together.

We've also added inference rules for the quantifiers, ∀ and
∃, which of course are not relevant in propositional logic 
but that are essential in predicate logic (whether first- or
higher-order).

We've also separate out, and present first, the fundamental
inference rules from "inference rules" that are can be proved
using the fundamental rules. These rules are thus "theorems,"
not "axioms." 
-/

/-
Ok. So each of the following lines does the following. As you
read this, look at the first definition, of and_introduction.

In Lean, we can use "def," a Lean keywork, to start to define
the meaning/value of a variable. After "def" comes the name of
the variable. Here it's and_introduction. Next comes what we
have already seen, albeit briefly: a type judgment, comprising
a colon followed by a type name. The type name in this case is
"Prop," which is the type of all *propositions* in Lean. So far
then we've told Lean that we're going to define and_introduction
to be a variable the value of which is a proposition. Next is 
a :=, which is the Lean operator for binding a value to a name.
Finally, the value to be bound is to the right. In this case,
as expected, it's a proposition. 

The particular proposition in this case is what we can call a 
"universal generalization" in that it starts with a ∀. The ∀ 
introduces two new variable names, X and Y, with a type judgment
stating that their values are propositions, indeed they can be
*any* propositions whatsoever. Finally, in the context of the
assumption that X and Y are arbitrary (any) proposition, the
rule states that if we assume that we are given a proof of X
(the analog of the assumption that X is true in propositional
or first-order predicate logic), and if in that context we then
further assume that we have a proof of Y (and thus that Y is 
also true), then in that context, we can construct a proof of
X ∧ Y, thus concluding that it, too, must be true.  
-/

/- *** AND *** -/

-- ∧ 
def and_introduction  : Prop  := ∀ (X Y : Prop), X → Y → (X ∧ Y)
def and_elim_left     : Prop  := ∀ (X Y : Prop), X ∧ Y → X  
def and_elim_right    : Prop  := ∀ (X Y : Prop), X ∧ Y → Y  

/-
Note that we are able to express these rules of logic very
naturally in higher-order constructive logic because we can
quantify over propositions. You cannot write these definitions
in first-order logic because it doesn't allow you to do this.
Such an expression is a syntax error in first-order logic. 
-/

/- A LEAN DETAIL and IMPORTANT LANGUAGE DESIGN CONCEPT
A good language gives you good ways not to repeat yourself.
We can avoid having to repeatedly write "∀ (X Y : Prop),"
by creating a "section" in a Lean file, and declaring the
common variables once at the top. Lean then implicitly adds
a "∀ (X : Prop)" at the beginning of any expression that has
an X in it (and the same goes for Y and Z in this file).
I
-/

section pred_logic

variables X Y Z : Prop

/-
In your mind, be sure to recognize that every one of the
following propositions now has an implicit ∀ in front. The
or_intro_left definition that comes next, for example, means 
def or_intro_left : Prop := ∀ (X Y : Prop), X → X ∨ Y. 
-/


/- *** OR *** -/

-- ∨ 
def or_intro_left : Prop    := X → X ∨ Y
def or_intro_right : Prop   := Y → X ∨ Y
def or_elim : Prop          := (X ∨ Y) → (X → Z) → (Y → Z) → Z

/-
Lean, and other languages like it, also allow you to drop
explicit type judgments when they can be inferred from the
context. In the rest of this file, we also drop the ": Prop"
explicit type judgments because Lean can figure our from the
values that follow the :='s that type types of the variables
here just have to be Prop.
-/

/-
Quiz questions. 

Suppose you know that (X → Z) and (Y → Z) are true and you 
want to prove Z. To be able to prove Z it will *suffice* to 
prove ______; for then you will need only to apply the ______
rule to deduce that Z is true.

Suppose you know that (X → Z), (Y → Z), and Z are all true.
Is it necessarily that case that (X ∨ Y) is also true? Defend
you answer.

Suppose it's raining OR the sprinkler is running, and that in
either case the grass is wet. Is the grass wet? How would you
prove it?
-/


/- *** IFF *** -/

-- ↔ 
def iff_intro         := (X → Y) → (Y → X) → X ↔ Y

/-
You can read this rule both forward (left to right) and 
backwards. Reading forwards, it says that if you have a
proof (or know the truth) of X → Y, and you have a proof
(or know the truth) of Y → X, then you can derive of a proof
(deduce the truth) of X ↔ Y.

The more important direction in practice is to read it
from right to left. What it says in this reading is that
if you want to prove X ↔ Y, then it will suffice to have
two "smaller" proofs: one of X → Y and one of Y → X. 

From now on, whenever you're asked to prove equivalence
of two propositions, X and Y, you'll thus start by saying,
"It will suffice to prove the implication in each direction."
Then you end up with two smaller goals to prove, one in 
each direction. So, "We first consider X → Y." Then give
a proof of it. Then, "Next we consider Y → X." Then give
a proof of it. And finally, "Having proven the implication
in each direction (by application of the rule of ↔ intro)
we've completed our proof. QED."
-/

def iff_elim_left     := X ↔ Y → (X → Y)
def iff_elim_right    := X ↔ Y → (Y → X)

/-
The elimination rules are also easy. Given X ↔ Y, you can
immediately deduce X → Y and Y → X.
-/

/- *** FORALL and ARROW *** -/

-- → and ∀ 
def arrow_all_equiv   := (∀ (x : X), Y) ↔ (X → Y)

/-
To prove either (∀ (x : X), Y) or (X → Y), you first assume  
that you're given an arbitrary but specific proof of X, and
in that context, you show that you can derive a proof (thus 
deducing the truth) of Y. It's exactly the same reasoning in
each case. This is the *introduction* rule for ∀ and →. 
-/

/-
In fact, in constructive logic, X → Y is simply a notation
*defined* as ∀ (x : X), Y. What each of these propositions 
states in constructive logic is that "From *any* proof, x, 
of X, we can derive a proof of Y." In fact, in Lean, these
propositions are not only equivalent but equal. 
-/

#check X → Y          -- Lean confirms this is a proposition
#check ∀ (x : X), Y   -- Lean understands this to say X → Y!



/- OPTIONAL
As an aside, here's a proof that these propositions are 
actually equal. This proof uses an inference rule, rfl, for 
equality that we've not yet studied. Don't worry about the 
"rfl" for now, but trust that we're giving a correct proof
of the equality of these two propositions in Lean
-/
theorem all_imp_equal : (∀ (x : X), Y) = (X → Y) := rfl 

/-
The reason it's super-helpful to know these propositions 
are equivalent is that it tells you that you can *use* a 
proof of a ∀ proposition or of a → proposition in exactly
the same way. So let's turn to the *elimination* rules for
→ and ∀. 
-/

def arrow_elim        := (X → Y)        → X   → Y
def all_elim          := (∀ (x : X), Y) → X   → Y

/-
The idea underlying these rules date to ancient times. 
They both say "if from the truth or a proof of X you 
can derive a proof or the truth of Y, and if you also 
have a proof, or know the truth, of X, then you can (in
constructive logic) derive a proof of Y (or deduce the
truth of Y." 

Here's an example. What we want to say in logic is
that if every ball is blue and b is some specific 
ball then b is blue. The elimination rule for ∀ and
→ applies a generalization to a specific instance to
deduce that the generalized statement specialized to
a particular instance is true.

Note: In this example, Y is a proposition obtained by 
plugging "x" into a one-argument predicate. So suppose 
(∀ (x : X), Y) is read as "for any Ball x, x is blue."  
Here X is "Ball;" x is an arbitrary but specific Ball; 
and Y is read as "x is blue." 
  
Now suppose that, in this context, you're given a 
*particular* ball, (b : X). What the overall rules
says is that you now conclude that "b is blue."

The elimination rule works by *applying* a proof of
a universal generalization (showing that something
is true of *every* object of a particular kind) to 
a *specific* object of that kind, to deduce that the 
generalized statement is also true of that specific
object.

If every ball is blue, and if b is a ball, then b
must be blue. Another way to say it that makes a
bit more sense for the (X → Y) notation is that 
"if being any ball, x, implies that x is blue, and 
if b is some particular ball, then b is blue.
-/

/-
As an example, consider a predicate, (isBlue _), where you can fill
in the blank/argument with any Ball-type object. If b is a specific
Ball-type object, then (isBlue b) is a proposition, representing the
English-language claim that b is blue. Here's how we represent this
predicate in Lean.
-/

variable Ball : Type            -- Ball is a type of object
variable isBlue : Ball → Prop
/-
First we Ball to be the name of a type of object (like int or 
bool). Then we define isBlue to be a construct (think function!)
that when given any object of type Ball as an argument yields a
proposition. To see how this works, suppose we have some specific
balls, b1 and b2.
-/
variables (b1 b2 : Ball)
/-
Now let's use isBlue to make some propositions!
-/
#check isBlue                               -- a predicate
#check isBlue b1                            -- a proposition about b1
#check isBlue b2                            -- a proposition about b2
#check (∀ (x : Ball), isBlue x)             -- generalization
variable all_balls_blue : (∀ (x : Ball), isBlue x)   -- proof of it
#check all_balls_blue b1                    -- proof b1 is blue
#check all_balls_blue b2                    -- proof b2 is blue

/-
Here's an English-language version.

Suppose b1 and b2 are objects of some type, Ball, and that isBlue 
is one-place predicate taking any Ball, b, as an argument, and that
reduces to a proposition, denoted (isBlue b), that we understand as
asserting that the particular ball, b, is blue. Next (295), we take
all_balls_blue as a proof that all balls are blue. Finally (296 and
297), we see that we can can use this proof/truth by *applying* it
to any particular ball, b, to obtain a proof/truth that b is blue. 

For any type S, given any X: (∀ s : S), T and any s : S, the ∀ 
and → elimination rule(s) say that you can derive a value/proof of 
type T; moreover this operation is basically done by *applying* ,
viewed as a function from parameter value to proposition, to the 
actual parameter, s (in Lean denoted as (X s)), to obtain a value
(proof) of (type) T. Modus ponens is like function application. In
constructive logic, a proof of the ∀ proposition *is* a function.
Here you begin to see how profound is that proofs in constructive 
logic tell you not only that a proposition is true but why. Here a
proof of X → Y or of ∀ (x : X), Y, is a program that when given any
value/proof of X as an argument returns a value/proof of Y. If you 
can produce a function that turns any proof of X into a proof of Y,
then you've shown that whenever X is true, so is Y; and that's just
what X → Y is meant to say (similarly for ∀ (x : X), Y). 
-/

/-
Walk-away message: Applying a proof/truth of a universal
generalization to a specific object yields a proof of the
generalization *specialized* to that particular object. That
is in the higher-order predicate logic of Lean. 
-/

/-
Finally, let's compare our elimination rule, in the higher-order
predicate logic of Lean, with its first-order logic counterpart.

There are two big differences, first, in first-order logic, you 
have to present the rule outside of the logic: you can't write 
rules like this, ∀ (X Y : Prop), X → Y → (X ∧ Y), in first-order
logic because in first order logic you can't quantify over types,
propositions, predicates, functions. Here we do just this with the
"∀ (X Y : Prop)." By contrast, in the higher-order logic of Lean,
we can represent the rules of first-order logic with no problem: 
e.g., "∀ (X Y : Prop), X → Y → (X ∧ Y)."

Second, as we've discussed, using Lean's higher-order logic, you
can think of a proof of "∀ (X Y : Prop), X → Y → (X ∧ Y)" as a 
function. Each variable bound by a ∀ and each implication premise
is an argument, with the type of the return value at the end of 
the line. So, here, a proof of this proposition can be taken as 
a function that takes two propositions, X and Y as arguments, then
a proof (value) of (type) X, then a proof (value) of type Y, and
that finally returns a proof (value) X ∧ Y. Whereas the proof of
∀ (X Y : Prop), X → Y → (X ∧ Y) is a function the returned proof
of (X ∧ Y) is a pair-like data structure. Proofs in constructive
logic are *computational*, and you can even compute with them, as
you do when you *apply* a proof of a certain kind to an argument
to obtain a resulting proof/value.
-/

/-
Quiz questions:

First-order logic. I know that every natural number is
beautiful (∀ n, NaturalNumber(n) → Beautiful(n) : true), 
and I want to prove (7 is beautiful : true). Prove it.
Name the inference rule and identify the arguments you
give it to prove it.

Constructive logic. Suppose I have a proof, pf, that every 
natural number is beautiful (∀ (n : ℕ), beautiful n), and I 
need a proof that 7 is beautiful. How can I get the proof 
I need? Answer in both English and with a Lean expression.

Formalize this story: All people are mortal, and Plato 
is a person, therefore Plato is Mortal.
-/

variable Person : Type
variable Plato : Person
variable isMortal : Person → Prop
variable everyoneIsMortal : ∀ (p : Person), isMortal p
#check (everyoneIsMortal Plato)   -- ∀ elimination!


/- *** TRUE AND FALSE *** -/

/-
In propositional logic, the literal expressions, true
and false, are part of the syntax of the logic, with
obvious interpretations. The "true" expression always
evaluates to Boolean true, and the "false" expression
to Boolean false. We could thus write expressions such
as (X ∨ false) and (X ∧ true).

In predicate logic we have the same concepts exactly. 
In first order predicate logic, true is a proposition
that is invariably judged to be true, and false is a
proposition that is invariable false. 

In the higher-order predicate logic defined in Lean,
true and false are also propositions, as we can see
with the following checks and an example.
-/

#check true
#check false
#check ∀ (P : Prop), P ∨ true

/-
As with all of the basic connectives and quantifiers,
the *meanings* of these terms are established by their
inference rules. We address the rules for each one now.
-/

/-
We want "true" to be a proposition that is always true.
In constructive logic, that means there's always a proof
of it. Indeed, in Lean, that proof is called true.intro. 
The way to prove that "true" is true is by giving this
proof as evidence.
-/

theorem true_is_true : true := true.intro

/-
In other words, there's always a trivial proof lying
around to prove that the proposition, "true," is true.
Let's decode that theorem:
- "theorem" says we're about to prove a proposition
- the proposition in this case is "true"
- and the proof is true.intro
The Lean prover accepts this proof as correct. It is.
Simply put, true.intro is the introduction rule for the
proposition, "true," in Lean.
-/

/-
What about the elimination rule for true? Well, having
a proof of true gives you essentially zero information,
so there's nothing useful you can really do with a proof
of true. Thus there is no elimination rule for true. 
-/

/-
Next, we want the inference rules for the proposition,
"false" to capture two ideas. First, the proposition
"false" must always be logically false. In first-order
logic, that's all there is to it. In the constructive
logic of Lean, the proposition "false," is logically
false *because it is defined to be a proposition that
has no proofs.* Because it has no proofs, there is no
introduction rule for "false." If there were, then we
would be able to use it to construct a proof of false,
which can't exist." There is thus *no possible way* to
complete the following definition.
-/

theorem a_proof_of_false : false := _   -- no can do!

/-
Now we get to the most interesting and important rule:
false elimination, or the elimination rule for "false."

As you recall, in propositional logic, false → X is
always true, no matter whether X is true or false.
So, false → false is true, and false → true is true.

Now suppose P is any proposition in first-order logic.
The elimination rule for "false" is false ⊢ P. In
other words, if you assume or have somehow proven 
false (which is possible from a false premise), then 
you can deduce that anything at all is true: including
P, no matter what proposition it is, even if it's a
false proposition. As they say, "from false anything
follows," or, in Latin, "ex falso quodlibet."

This principle makes good sense, because if false is
true (the premise), then even if a proposition, P, is 
false, false is true, so P is true (too)!
-/

/-
A little practice. Which of the following propositions
in predicate logic is true?
-/

def p1 : Prop := false → false
def p2 : Prop := false → true
def p3 : Prop := true → true
def p4 : Prop := true → false
def p5 : Prop := false → 2 = 3
def p6 : Prop := false → 0 = 0
def p7 : Prop := ∀ (P : Prop), true → P
def p8 : Prop := ∀ (P : Prop), false → P 

theorem p8_is_true : p8 := 
begin
unfold p8,
assume P,
assume f,
apply false.elim f,
end 

/-
For each proposition, state whether it's true or false
then give a proof of it (in English). Here are some formal
proofs to help.
-/

-- def p1 : Prop := false → false
theorem x : p1 := 
begin
  unfold p1,
  assume f : false,
  exact f,
end

-- false → true
example : p2 := 
begin
  unfold p2,
  assume f,           -- move premise into context
  --exact true.intro,   -- don't have to use assumption
  -- apply false.elim f,
  contradiction,
end

example : p3 := 
begin
unfold p3,
assume t,
exact t,    -- exact true.intro also works
end

example : p4 := 
begin
unfold p4,
assume t,
end

example : p5 := 
begin
unfold p5,
assume f,
cases f,
end

example : p6 := 
begin
unfold p6,
assume f,
cases f,
-- exact rfl,
end
/-
What? The cases tactic applies the elimination rule to
an assumed or derived proof of false. For each of the 
ways that the proof, f, could have been constructed,
you have a case to consider; but there are no ways a
proof of false can be constructed so you have no cases
to consider, so the proof is done! This is another way
to understand how/why false elimination works in the
constructive logic of Lean and other similar tools. 
-/

example : p7 := 
begin
unfold p7,
intro P,
assume t,
-- stuck
end

example : p8 := 
begin
unfold p8,
assume P f,
cases f,
end

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
there is no proof of P*. 

Now here's the slightly tricky way that we show that there can
be no proof of P. We show (P → false). What this proposition
says is that "If there is a proof of P, then from it we can
derive a proof of false." But a proof of false doesn't exist,
so if we prove (P → false) is true then there must be no proof
of P. In other words, to prove there is no proof of P, we prove
P → false! And that leads to our definition of ¬P. What it means
is *exactly* P → false. 
-/
def not_ (X : Prop) := X → false  -- the definition of "not" (¬)

/-
Examples
-/

example : 0 = 1 → false :=
begin
assume h,   -- suppose 0 = 1
cases h,    -- that can't happen, no cases, we've proved ¬(0=1)
end 

example : ¬(0 = 1) :=
begin 
assume h,
cases h,
/-
Remember!!!  0 ≠ 1 means ¬(0 = 1) means 0 = 1 → false. You 
must remember that when you want to prove ¬P, that means you
need to prove P → false: that a proof of P is a contradiction.  
to remember this, because it tells you how to prove it. To
show it, assume the premise, 0 = 1, then show that in this
context, there is a contradiction ---given our intuitive
grasp of equality and the natural numbers. 

If you can derive a contradiction, that is tantamount to a 
proof of false, and from a proof of false, f, the truth of
any other proposition follows. Put another way, in terms of
Lean's formal logic, the term, (false.elim f), where f is a
proof of false, serves is a formal proof of any proposition.
-/
end

/- PROOF BY NEGATION 

What we have now seen is a crucial "proof strategy" often 
called proof by negation. To show ¬P, that the statement, 
P is false, is true, prove P → false. First assume that 
P is true (you have a proof of it) and show that in this
context, you can derive a proof of false. You will often
do this by producing a contradiction, which is proofs of
both X and ¬X for some proposition, from which, as we will
see shortly, you can derive a proof of false by applying
the rule of arrow elimination (function application!).  
-/

/-
HW #3 Exercise: state and prove the rule (the "theorem") 
of "no contradiction:" first in English and then in the
predicate logic of Lean. Or if you prefer, work it out 
in Lean and the write it in English. The formal statement
of the proposition is in the partially completed theorem 
below. 
-/

theorem no_contra : ¬(X ∧ ¬X) :=
begin
end

/-
Hint: The proof uses arrow introduction (you have to prove an
implication), "and" elimination (you need separate proofs of X
and ¬X; try using cases in Lean), and arrow elimination (you
need to *use* these proofs, one of which, remember, is a proof
of an implication; so what can you do with that?). 
-/


/- COMING SOON -/


def excluded_middle   := X ∨ ¬X   -- not an axiom in CL
def neg_elim          := ¬¬X → X  -- depends on axiom of e.m.




/- Under Construction -/

/-
And for this explanation, we need to be precise about what it means
to be a predicate in predicate logic. As we've exaplained before, 
a predicate is a proposition with one or more parameters. Think of
parameters as blanks in the reading of a proposition that you can
fill in with any value of the right type for that slot. When you 
fill in all the blanks, which you do by by applying the predicate
to actual parameter values, you get back a proposition: a specific
statement about specific objects with no remaining parameters to
be filled in. A predicate thus gives rise to a whole *family* of 
propositions, one for each possible combination of argument values. 
Once all the parameters in a predicate are fixed to actual values,
you've no longer got a predicate but just a proposition. 
-/


-- ∃
def exists_intro := ∀ {P : X → Prop} (w : X), P w → (∃ (x : X), P x) 
def exists_elim := ∀ {P : X → Prop}, (∃ (x : X), P x) → (∀ (x : X), P x → Y) → Y 

/-
That's it for the fundamental rules of higher-order predicate
logic. The constructive logic versions of the remaining inference
rules we saw in propositional logic are actually theorems, which
means that they can be proved using only the fundamental rules,
which we accept as axioms. An axiom is a proposition accepted as
true without a proof. The inference rules of a logic are accepted
as axioms. The truth of any other proposition in predicate logic
(the foundation for most of mathematics) is proved by applying 
fundamental axioms and previously proved theorems..  
-/

-- theorems
def arrow_trans       := (X → Y) → (Y → Z) → (X → Z)
def contrapostitive   := (X → Y) → (¬Y → ¬X)
def demorgan1         := ¬(X ∨ Y) ↔ ¬X ∧ ¬Y
def demorgan2         := ¬(X ∧ Y) ↔ ¬X ∨ ¬Y
def no_contradiction  := ¬(X ∧ ¬X)


/-
Here are the logical fallacies we first met in propositional
logic, now presented in the much richer context of constructive
logic. You might guess that it will be impossible to construct
proofs of these fallacies, and you would be correct, as we will
see going forward.
-/
-- fallacies
def converse          := (X → Y) → (Y → X)
def deny_antecedent   := (X → Y) → ¬X →  ¬Y
def affirm_conclusion := (X → Y) → (Y → X)
def affirm_disjunct   := X ∨ Y → (X → ¬Y)

end pred_logic