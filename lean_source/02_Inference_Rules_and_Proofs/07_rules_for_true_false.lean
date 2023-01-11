/- TEXT:
**************
True and False
**************
TEXT. -/

-- QUOTE:
section pred_logic
variables X Y Z : Prop
-- QUOTE.


/- TEXT:
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
TEXT. -/

-- QUOTE:
#check true
#check false
#check ∀ (P : Prop), P ∨ true
-- QUOTE.

/- TEXT:
As with all of the basic connectives and quantifiers,
the *meanings* of these terms are established by their
inference rules. We address the rules for each one now.
TEXT. -/

/- TEXT:
We want "true" to be a proposition that is always true.
In constructive logic, that means there's always a proof
of it. Indeed, in Lean, that proof is called true.intro. 
The way to prove that "true" is true is by giving this
proof as evidence.
TEXT. -/

-- QUOTE:
theorem true_is_true : true := true.intro
-- QUOTE.


/- TEXT:
In other words, there's always a trivial proof lying
around to prove that the proposition, "true," is true.
Let's decode that theorem:
- "theorem" says we're about to prove a proposition
- the proposition in this case is "true"
- and the proof is true.intro
The Lean prover accepts this proof as correct. It is.
Simply put, true.intro is the introduction rule for the
proposition, "true," in Lean.
TEXT. -/

/- TEXT:
What about the elimination rule for true? Well, having
a proof of true gives you essentially zero information,
so there's nothing useful you can really do with a proof
of true. Thus there is no elimination rule for true. 
TEXT. -/

/- TEXT:
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
TEXT. -/

-- QUOTE:
theorem a_proof_of_false : false := _   -- no can do!
-- QUOTE.

/- TEXT:
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
TEXT. -/

/- TEXT:
A little practice. Which of the following propositions
in predicate logic is true?
TEXT. -/

-- QUOTE:
def p1 : Prop := false → false
def p2 : Prop := false → true
def p3 : Prop := true → true
def p4 : Prop := true → false
def p5 : Prop := false → 2 = 3
def p6 : Prop := false → 0 = 0
def p7 : Prop := ∀ (P : Prop), true → P
def p8 : Prop := ∀ (P : Prop), false → P 
-- QUOTE.

-- TEXT:
Let's look at the case of p8. Prove that it's true.
-- TEXT.

-- QUOTE:
theorem p8_is_true : p8 := 
begin
unfold p8,
assume P,
assume f,
apply false.elim f,
end 
-- QUOTE.

/- TEXT:
For each proposition, state whether it's true or false
then give a proof of it (in English). Here are some formal
proofs to help.
TEXT. -/

-- QUOTE:
-- def p1 : Prop := false → false
theorem x : p1 := 
begin
  unfold p1,
  assume f : false,
  exact f,
end
-- QUOTE.

-- QUOTE:
-- false → true
example : p2 := 
begin
  unfold p2,
  assume f,           -- move premise into context
  --exact true.intro,   -- don't have to use assumption
  -- apply false.elim f,
  contradiction,
end
-- QUOTE.

-- QUOTE:
example : p3 := 
begin
unfold p3,
assume t,
exact t,    -- exact true.intro also works
end
-- QUOTE.

-- QUOTE:
example : p4 := 
begin
unfold p4,
assume t,
end
-- QUOTE.

-- QUOTE:
example : p5 := 
begin
unfold p5,
assume f,
cases f,
end
-- QUOTE.

-- QUOTE:
example : p6 := 
begin
unfold p6,
assume f,
cases f,
-- exact rfl,
end
-- QUOTE.

/- TEXT:
What? The cases tactic applies the elimination rule to
an assumed or derived proof of false. For each of the 
ways that the proof, f, could have been constructed,
you have a case to consider; but there are no ways a
proof of false can be constructed so you have no cases
to consider, so the proof is done! This is another way
to understand how/why false elimination works in the
constructive logic of Lean and other similar tools. 
TEXT. -/

-- QUOTE:
example : p7 := 
begin
unfold p7,
intro P,
assume t,
-- stuck
end
-- QUOTE.

-- QUOTE:
example : p8 := 
begin
unfold p8,
assume P f,
cases f,
end
-- QUOTE.
