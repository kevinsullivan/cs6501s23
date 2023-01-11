section pred_logic

variables X Y Z : Prop

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

/- Quick exercise. Give a proof of this (in English, and 
give it a try in Lean as well.
-/

def arrow_trans       := (X → Y) → (Y → Z) → (X → Z)

end pred_logic
