/- TEXT:
In mathematics the way we establish the truth of any
given proposition is to show a proof of it, rooted in
first principles. The first of the first principles are 
the *axioms* of the logic. To be fluent in the axioms
of a logic is to know it.

The main aim of this chapter is to teach you the axioms
of the higher-order predicate logic embedded in Lean, as
defined in the standard Lean libraries. 

We'll need to establish a few new technical ideas to
have the tools needed to present the main content. The
good news is that the axioms of this predicate logic
just generalize the axioms of propositional logic. 

You already have a reasonable intuitive grasp of the
meanings of the connectives in propositional logic.
Predicate logic uses the same connectives to compose
given propositions into new ones, with the same basic
meanings. For example, we still have one introduction
(construction) rule for ∧ and two elimination rules. 

Key differences, already discussed in class, are that
propositions are now types, their values (if they have
any) are proofs, and inference rules are re-cast in
terms of proof/type judgments rather than in terms of
*truth* judgments.

For example, instead of *P* and *Q* being of type
*prop_expr*, we now have them being of type *Prop*.
They are types that encode logical propositions. And
whereas the *and_intro* rule in propositional logic is
(⟦P⟧ i = tt) → (⟦Q⟧ i = tt) → (⟦P ∧ Q⟧ i = tt), now it
is *∀ (P Q : Prop), P → Q → and P Q*. ∧ is notation
for *and.* 

Read this as a function, polymorphic in types *P* 
and *Q*, taking further arguments p, of type (a 
proof of) P, and q, a proof of Q, and returning a 
proof P ∧ Q. In this case, the returned proof object
stores the pair of proofs, *p* and *q*.
TEXT. -/
