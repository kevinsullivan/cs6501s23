****************************
Higher-Order Predicate Logic
****************************

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
