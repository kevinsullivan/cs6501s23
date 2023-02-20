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

.. code-block:: lean

  #check true                   -- a proposition
  example : true := true.intro  -- a proof of it

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

.. code-block:: lean

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

.. code-block:: lean

  structure and (A B : Prop) : Prop :=
  intro :: (left : A) (right : B)

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

.. code-block:: lean

  example (b : bool) :  bnot (bnot b) = b :=
  begin
  cases b,              -- NB: one case per constructor
  repeat { apply rfl }, -- prove goal *in each case*
  -- QED.               -- thus proving it in *all* cases
  end

Turning to a proof of a conjunction, *A ∧ B*, only two
small details change. First, there *and* has just one
constructor. So when we do case analysis, we'll get only
one case to consider. Second, the constructor now takes
two arguments, rather than zero as with tt and ff. So,
in that one case, we'll be entitled to assume that the
two proof arguments must have been given. These will be
the *left* and *right* proofs of *A* and *B* separately. 

.. code-block:: lean

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

or ∧ 
----

- def or_intro_left_rule := (⟦X⟧ i = tt) → (⟦(X ∨ Y)⟧ i = tt) 
- def or_intro_right_rule := (⟦Y⟧ i = tt) → (⟦(X ∨ Y)⟧ i = tt) 
- def or_elim_rule :=   (⟦(X ∨ Y)⟧ i = tt) → (⟦(X => Z)⟧ i = tt) → (⟦(Y => Z)⟧ i = tt) → (⟦(Z)⟧ i = tt)

Just as with ∧, the ∨ connective in Lean is represented as
a logical type, polymorphic in two propositional arguments. 

.. code-block:: lean

  inductive or (A B : Prop) : Prop
  | inl (h : A) : or
  | inr (h : B) : or
  end hidden

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

.. code-block:: lean

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

.. code-block:: lean

  -- or.elim : ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
  -- deduce c from proofs of a ∨ b, a → c, and b → c, 
  #check @or.elim 
  
  example (P Q R : Prop) : P ∨ Q → (P → R) → (Q → R) → R
  | (or.inl p) pr qr := pr p
  | (or.inr q) pr qr := qr q
  


.. code-block:: lean

  /-
  -- formalize the rest
  -- 9. ¬¬X ⊢ X                 -- negation elimination
  -- 10. X → ⊥ ⊢ ¬X             -- negation introduction
  -- 11. (X ⊢ Y) ⊢ (X → Y)      -- a little complicated
  -- 12. X → Y, X ⊢ Y           -- arrow elimination
  -- 13. X → Y, Y → X ⊢ X ↔ Y    -- iff introduction
  -- 14. X ↔ Y ⊢ X → Y          -- iff elimination left
  -- 15. X ↔ Y ⊢ Y → X          -- iff elimination right

