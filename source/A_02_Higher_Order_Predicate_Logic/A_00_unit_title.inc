===============
Predicate Logic
===============

.. code-block:: lean

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

Now we'll turn to the idea that propositions are types of 
a special kind. In Lean and related proof assistants and in
type theory more generally, propositions are represented as 
*types* that inhabit their own type universe: on called Prop.

.. code-block:: lean

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

.. code-block:: lean

  variables (P Q R : Prop)
  example : P ∧ Q → P := 
  begin intro h; apply and.elim_left h 
  end

version of the and-elimination-left inference rule from 
from the last chapter. The major task of this chapter is
to "lift" your already established understanding of the
inference rules of propositional logic to the level of
higher-order constructive logic. Along the way we'll see
a few places where the classical rules break down.
*********
Functions
*********
**********
Predicates
**********
***********
Connectives
***********

We get them all from predicate logic, with meanings
defined by inference rules that straightforwardly 
generalize those from propositonal logic.

.. code-block:: lean

  def x := 5 -- ignore this

***********
Quantifiers
***********

Among which are quantifiers over types giving rise to
parametric polymorphism, where the type of element that
is handled by an operation can vary with no changes in
the definition of the operation itself.

.. code-block:: lean

  def y := 5 -- ignore this

***************
Inference Rules
***************

.. code-block:: lean

  def z := 5 -- ignore this


.. code-block:: lean

  def w := 5 -- ignore this

