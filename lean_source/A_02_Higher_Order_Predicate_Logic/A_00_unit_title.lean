/- TEXT:
===============
Predicate Logic
===============
TEXT. -/


/-
The term, *predicate logic*, used informally, is usually taken to 
refer to first-order predicate logic (often extended with theories, 
e.g., of natural number arithmetic). However, in this course, you
will learn higher-order constructive predicate logic. First-order
logic is a special restricted case. 

We've organized the course so far to prepare you to quickly pick
up higher-order predicate logic as it's *embedded* in the logic of
the Lean prover, by definitions provided by *mathlib*, Lean's main
library of mathematical definitions.

Major similarities and changes include the following:
- Propositions become types, not just logical expressions
- Truth judgments (⟦E⟧ i = tt) replaced by proof judgments (e : E)
- Functions and applications are essential parts of predicate logic 
- Predicates are functions from values to propositions *about them*
- We adopt all of the usual propositional logic connectives 
- We adopt generalized versions of the usual inference rules
- We gain two new ones: universal and existential quantifiers
- We gain new inference rules for the ∀ and ∃ quantifiers 
- Generalizing (∀) over types gives us parametric polymorphism
TEXT. -/

/-
**********************
Propositions are Types
**********************

In the last chapter, we build on all of the ideas of
the last chapter to gain an understanding of higher
order predicate logic in Lean. Each section of this
chapter focuses on a dimension in which the latter is
different, often a powerful generalization, of ideas
from the last chapter.

As an example, in the last chapter, we represented
propositions as terms of our data type, *prop_expr*. 
We  also saw that we could formulate inference rules of 
propositional logic to provide a way to reason about
the truth of given propositions. In this chapter, we
will represent propositions as types of a special kind,
instead, and proofs as values of these types. We will
then adopt exacty the same inference rules we saw in
the last chapter, but generalized to this far more
expressive logic.   


To warm up for the idea that propositions are (represented as)
types (in type theory), as an example we'll first look at the 
types related to the natural number, 1. Then we'll analyze the
types of a few propositions, namely 1 = 1 and 0 = 1. The take
away message will be that propositions are special types that
live in their own *type universe* and values of such types (if
there are any) serve as *proofs* of such propositions. 

Computational Types
-------------------
-/

-- QUOTE:
-- The type of 1 is nat 
#check 1

-- Type type of nat is *Type*
#check nat 

-- The type of all basic computational types is *Type*
#check bool
#check string
#check list bool

-- A natural question: What's the type of Type, etc?
#check Type 
#check Type 0   -- Type is shorthand for Type 0
#check Type 1   -- It's type universes all the way up
#check Type 2   -- etc.

/-
What we have so far then is a hierarchy of "computational"
types like this:

       ...        higher type universes
        |
      Type 1 (the type of objects that contains Type 0 objects)
        |
      Type 0         a type universe
        |        
       nat                type
        |
        1                value
-/

/- Type n+1 is the type of objects that contain objects of type Type n -/
#check list nat        -- list of nats : Type 0
#check list (Type 0)   -- list of Type 0s : Type 1  
#check list (Type 1)   -- list of Type 1s : Type 2
-- QUOTE.

/- TEXT: 
Now we'll turn to the idea that propositions are types of 
a special kind. In Lean and related proof assistants and in
type theory more generally, propositions are represented as 
*types* that inhabit their own type universe: on called Prop.
TEXT. -/

#check 1 = 1  -- 1 = 1 is a proposition, thus of type Prop
#check ∃ (a b c : ℕ), a*a + b*b = c*c -- also of type Prop

/-
So just as *Type* (*Type 0*) is the type of all basic data
types, *Prop* is the type of all propositions. And just as
data types can have values (as nat has the value 1), so can
propositional types have values: these, if they exist, serve
as *proofs* of their propositions.

For example, the proposition/type, *1 = 1*, in Lean does 
have a proof value, namely (eq.refl 1). So what is its 
type? Well it's type is *1 = 1*. Let's see.
TEXT. -/

-- QUOTE: 
-- Example: Here's a proof of 1 = 1
def proof_of_1_eq_1 := eq.refl 1

-- What is its type?
#check proof_of_1_eq_1

/- Types have types, too. Each proposition is its own
type, but all such types in turn are of type, Prop. In
fact, Prop is the type of propositions in Lean. We we
have the following picture of the type hierarchy for the
terms we've just constructed.
-/

-- type is 1 = 1
#check proof_of_1_eq_1

-- type is Prop
#check 1 = 1

-- QUOTE.


/- TEXT:
*******************
From Truth to Proof
*******************


In the last chapter, we defined inference rules for
propositional logic in terms of *truth judgments*. For
example, (⟦ P ∧ Q ⟧ i == tt) → ⟦ P ⟧ i = tt (one of the
elimination rules for conjunctions.) In the logic of
Lean, we reason in terms of *proof* judgments. If *P*
is a proposition, then (p : P) is a proof of P, and we
now reformulate the inference rules to operated not on
truth judgments but on proofs. For example, we'll now
have *∀ (P Q: Prop), P ∧ Q → P*. This says that if *P* 
and *Q* are arbitrary propositions, then from any proof
(value), *(pq : P ∧ Q)*, you can derive/produce/deduce a 
value/proof of *P*. 
TEXT. -/

-- QUOTE:
variables (P Q R : Prop)
example : P ∧ Q → P := 
begin intro h; apply and.elim_left h 
end
-- QUOTE.

/- TEXT: This new inference rule is just an "upgraded"
version of the and-elimination-left inference rule from 
from the last chapter. The major task of this chapter is
to "lift" your already established understanding of the
inference rules of propositional logic to the level of
higher-order constructive logic. Along the way we'll see
a few places where the classical rules break down.
TEXT. -/



/- TEXT:
*********
Functions
*********
TEXT. -/

/- TEXT:
**********
Predicates
**********
TEXT. -/

/- TEXT:
***********
Connectives
***********

We get them all from predicate logic, with meanings
defined by inference rules that straightforwardly 
generalize those from propositonal logic.
TEXT. -/

-- QUOTE:
def x := 5 -- ignore this
-- QUOTE.

/- TEXT:
***********
Quantifiers
***********

Among which are quantifiers over types giving rise to
parametric polymorphism, where the type of element that
is handled by an operation can vary with no changes in
the definition of the operation itself.
TEXT. -/

-- QUOTE:
def y := 5 -- ignore this
-- QUOTE.


/- TEXT:
***************
Inference Rules
***************
TEXT. -/

-- QUOTE:
def z := 5 -- ignore this
-- QUOTE.

/-
******
Proofs
******
-/

-- QUOTE:
def w := 5 -- ignore this
-- QUOTE.

/-
********
Theorems
********
-/



