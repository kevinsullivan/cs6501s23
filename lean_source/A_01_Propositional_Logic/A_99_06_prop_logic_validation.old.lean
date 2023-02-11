/- TEXT:

************************************
Algebraic Axioms and Inference Rules
************************************

We've now seen that it's not enough to prove a few 
theorems about a construction (here our syntax and 
semantics for propositional logic). We know this is
true because we did so yet without being blocked by
the bug we introduced in the definition of *bimp*.

So how can we confirm *for sure* that our model (or
implementation) of propositional logic is completely
valid? What are *all* the properties or constraints
that our model has to possess or satisfy?

In this class we'll clarify two different methods.
First, we can show that our specification satisfies
the *algebraic axioms* of propositional logic. Second,
we can prove that all of the *inference rules* of the
logic are valid in our representation of the logic.

Along the way we'll take the opportunity to see more
of what Lean can do for us:
- A Scott/semantic bracket notation for *pEval*
- declare automatically introduced variables in sections
- using implicit arguments to further improve readability

We'll also see that proofs of universally quantified 
propositions are basically functions with the quantified
variables as the arguments. Such a proof can be applied
to such arguments to produce proof of the proposition
specialized by application to the given arguments.  

To avoid duplication of code from the last chapter,
we'll import all of the definitions in its Lean file
for use here.
TEXT. -/

-- QUOTE:
-- Please briefly revisit especially prop_expr and pEval
import .A_05_prop_logic_properties
namespace cs6501
-- QUOTE.

/- TEXT:
Algebraic Properties
--------------------

First, a propositional logic can be understood as an algebra over
Boolean-valued terms, variables, and constants. Constants and variables
are are terms, but terms can also be constructed from smaller terms using
connectives: ∧, ∨, ¬, and so on. The axioms of propopsitiona logic impose
constraints on how these operations behave, on their own and combined. 

The constraints are algebraic, just as the axioms are algebraic that
impose the standard ring structure on the natural numbers. These are 
the *usual* commutativity and associativity properties of natural number
addition and multiplication, the distributivity of multiplication over 
addition, and so forth. As we go through the required properties for 
propositional logic, note the common underlying algebraic structure.  

Commutativity
-------------

The first two axioms that that the and and or operators 
(∧, ∨) are commutative. One will often see these rules
written as follows:

- (p ∧ q) = (q ∧ p)
- (p ∨ q) = (q ∨ p)

To be completely formal, we need to be a more careful. 
First, we need to define variables such as p and q as 
being universally quantified. Second, we need to make clear 
that the quantities that are equal are not the propositions
themselves (they are not equal) but their *meanings* under 
all interpretations. Thus in the last chapter we defined
the commutativity of ∧ like this:
TEXT. -/  

-- QUOTE:
example : 
∀ (p q : prop_expr) (i : prop_var → bool),
  pEval (p ∧ q) i = pEval (q ∧ p) i :=
and_commutes  -- proof from last chapter
-- QUOTE.

/- TEXT:
As we've seen, mathematical theories are often
augmented with concrete syntax / notations that 
make it practical for people to read and write 
such mathemantics. 

A standard notation for a "meaning-of-expression" 
operator is a pair of *denotation* or *Scoot* 
brackets. So *⟦ e ⟧* can be read as "the meaning
of *e*." To resolve meaning, an interpretation, 
*i*. We'll thus write *⟦ e ⟧ i* to mean the meaning
of e under the interpretation i: *pEval e i*. 
TEXT. -/

-- QUOTE:

notation (name := pEval) ` ⟦ ` p ` ⟧ `  :=  pEval p


/-
We can declare a set of variables to be used across
multiple definitions within a section. 
-/
section prop_logic_axioms

-- Let p, q, r, and i be arbitrary expressions and an interpretation
variables (p q r : prop_expr) (i : prop_var → bool)

-- now we can write expressions with these variables without explicitly introducing them by ∀ 
-- we add prime marks just to avoid naming conflicts, the primes have no special meaning here
def and_commutes' := ⟦(p ∧ q)⟧ i = ⟦(q ∧ p)⟧ i 
def or_commutes' :=  ⟦(p ∧ q)⟧ i = ⟦(q ∧ p)⟧ i

/-
Comparing the types of our initial proof that and 
commutes with our new definition shows that they are
same if you understand that ∀-quantified variables
to be the same as function arguments. 
-/
#check and_commutes
#check and_commutes'

/-
Observe: We can *apply* these theorems
to particular objects to specalize the
generalized statement to the particular
objects.
-/

variables (a b : prop_expr)
#reduce and_commutes' p q i
#reduce and_commutes' a b i


-- re-doing proof with new notation
example : and_commutes' p q i := 
begin
-- expand definitions
unfold and_commutes',
unfold pEval bin_op_sem,
-- rest by case analysis as usual
sorry,
end 
-- QUOTE.

/- TEXT: 
Associativity
-------------
TEXT. -/

-- QUOTE:
def and_associative_axiom :=  ⟦(p ∧ q) ∧ r⟧ i = ⟦(p ∧ (q ∧ r))⟧ i
def or_associative_axiom :=   ⟦(p ∨ q) ∨ r⟧ i = ⟦(p ∨ (q ∨ r))⟧ i
-- QUOTE.

/- TEXT:
Distributivity
--------------
TEXT. -/

-- QUOTE:
def or_dist_and_axiom := ⟦p ∨ (q ∧ r)⟧ i = ⟦(p ∨ q) ∧ (p ∨ r)⟧ i
def and_dist_or_axiom := ⟦p ∧ (q ∨ r)⟧ i = ⟦(p ∧ q) ∨ (p ∧ r)⟧ i
-- QUOTE.

-- Homework

/- TEXT:
DeMorgan's Laws
---------------
TEXT. -/

-- QUOTE:
def demorgan_not_over_and_axiom := ⟦¬(p ∧ q)⟧ i = ⟦¬p ∨ ¬q⟧ i
def demorgan_not_over_or_axiom :=  ⟦¬(p ∨ q)⟧ i = ⟦¬p ∧ ¬q⟧ i
-- QUOTE.

-- Homework

/- TEXT:
Negation
--------
TEXT. -/

-- QUOTE:
def negation_elimination_axiom := ⟦¬¬p⟧ i = ⟦p⟧ i
-- QUOTE.


/- TEXT:
Excluded Middle
---------------
TEXT. -/

-- QUOTE:
def excluded_middle_axiom := ⟦p ∨ ¬p⟧ i = ⟦⊤⟧ i   -- or just tt
-- QUOTE.


/- TEXT:
No Contradiction
----------------
TEXT. -/

-- QUOTE:
def no_contradiction_axiom := ⟦p ∧ ¬p⟧ i = ⟦⊥⟧ i   -- or just tt
-- QUOTE.


/- TEXT:
Implication
-----------
TEXT. -/

-- QUOTE:
def implication_axiom := ⟦(p => q)⟧ i = ⟦¬p ∨ q⟧ i  -- notation issue


example : implication_axiom a b i := 
begin
unfold implication_axiom pEval bin_op_sem un_op_sem,
cases ⟦ a ⟧ i,
cases ⟦ b ⟧ i, 
apply rfl,  -- Yay, now we can build a proof!!! 
apply rfl,
cases ⟦ b ⟧ i, 
apply rfl,
apply rfl,
-- = bnot ( ⟦ a ⟧ i) || ⟦ b ⟧ i
end

-- QUOTE.


/- TEXT:
And Simplification
------------------

- p ∧ p = p
- p ∧ T = p
- p ∧ F = F
- p ∧ (p ∨ q) = p

TEXT. -/


/- TEXT:
Or Simplification
------------------

- p ∨ p = p
- p ∨ T = T
- p ∨ F = p
- p ∨ (p ∧ q) = p

TEXT. -/

/- TEXT:
Inference Rules
===============

Key idea: These are rules for reasoning about evidence.
What *evidence* do you need to derive a given conclusion?
These are the "introduction" rules. From a given piece of
evidence (and possibly with additional evidence) what new
forms of evidence can you derive? These are "elimination"
rules of the logic.
TEXT. -/

-- QUOTE:
-- 1. ⊢ ⊤                     -- true introduction
-- 2. ⊥, X ⊢ X                -- false elimination

-- 3. X, Y ⊢ X ∧ Y            -- and_introduction
-- 4. X ∧ Y ⊢ X               -- and_elimination_left
-- 5. X ∧ Y ⊢ Y               -- and_elimination_right

-- 6. X ⊢ X ∨ Y               -- or introduction left
-- 7. Y ⊢ X ∨ Y               -- or introduction right
-- 8. X ∨ Y, X → Z, Y → Z ⊢ Z -- or elimination

-- 9. ¬¬X ⊢ X                 -- negation elimination
-- 10. X → ⊥ ⊢ ¬X              -- negation introduction

-- 11. (X ⊢ Y) ⊢ (X → Y)      -- a little complicated
-- 12. X → Y, X ⊢ Y           -- arrow elimination

-- 13. X → Y, Y → X ⊢ X ↔ Y    -- iff introduction
-- 14. X ↔ Y ⊢ X → Y          -- iff elimination left
-- 15. X ↔ Y ⊢ Y → X          -- iff elimination right
-- QUOTE.

/- TEXT:
In the style we've developed, formally state and prove 
that our logic and semantics has each of the properties, 
1, 2, 4, 5, 6, 8, 9, 10, 12, and 15. Identify any rules 
that fail to be provable due to the injected bug in bimp.

Use Lean's *theorem* directive to give names to proofs. 
as names for your proofs, use the names in the comments
after each rule (adding missing underscores as needed).

To do this part of the assignment, make a copy of this
file from the class repo and add the statement and proof
of each theorem below. You will turn in the file with these
proofs included in the given order at the end of the file.

This isn't a comprehensive list of properties. We lack
rules for ⊤ and ⊥ (formerly True, False; still terms 
that invariably evaluate to true (tt) and false (ff).
There are rules that explain, for example, that ⊤ ∧ e 
is equivalent to e; ⊥ ∧ e is invariably false; ⊥ or e 
is equivalent to e; and ⊤ ∨ e is invariably true. Go 
ahead and prove these propositions as well if you just
can't stop proving! (optional :-).

Try to do all or at least most of this assignment on 
your own. Feel free to ask for or give help on minor
matters, e.g., of Lean syntax, or if some concept isn't
yet clear enough. Discussing such issues is constructive. 
I skipped over properties whose proofs look almost just
like those for closely related properties.
TEXT. -/
-- QUOTE:
end prop_logic_axioms
end cs6501
-- QUOTE.
