
.. code-block:: lean

  import .A_05_prop_logic_properties
  namespace cs6501

****************
Algebraic Axioms
****************

We've now seen that it's not enough to prove a few 
theorems about a construction (here our syntax and 
semantics for propositional logic). 

So how will we confirm *for sure* that our model (or
implementation) of propositional logic is completely
valid? 

We'll offer two different methods. First, in this 
chapter, we'll prove that our specification satisfies
the *algebraic axioms* of propositional logic. Second,
in the next chapter, we'll prove that the *inference 
rules* of propositional logic are valid in our model.

Along the way we'll take the opportunity to see more
of what Lean can do for us:
- Scott/semantic bracket notation for *meaning-of*
- declare automatically introduced variables
- use of implicit arguments to further improve notation
- universally quantified variables are function arguments 
- "sorry" to bail out of a proof and accept proposition as axiom

To avoid duplication of code from the last chapter,
we'll import all of the definitions in its Lean file
for use here.
Algebraic Properties
--------------------

First, a propositional logic can be understood as an *algebra* with
Boolean-valued (as opposed to numeric) terms, variables, and constants. 
Constants and variables are are terms, but terms are also  constructed
from smaller terms using connectives: ∧, ∨, ¬, and so on. The axioms of 
propopsitions define how these operations work, on their own and when 
combined. 

These algebraic properties of propositional logic are very much akin
to the usual commutativity, associativity, distributivity, identity,
and other such properties of the natural numbers and the addition and 
multiplication operations on them. As we go through the analogous 
properties for propositional logic, note the common properties of both 
algebras.  


Commutativity
-------------

The first two axioms that that the and and or operators 
(∧, ∨) are commutative. One will often see these rules
written in textbooks and tutorials as follows:

- (p ∧ q) = (q ∧ p)
- (p ∨ q) = (q ∨ p)

This kind of presentation hides a few assumptions. First,
it assumes p and q are taken to be arbitrary expressions
in propositional logic. Second, it assumes that what is
really being compared here are not the expressions per se
but their semantic meanings. Third it assumes that equality
of meanings hold under all possible interpretations. 

To be completely formal in Lean, we need to be explicit
about these matters. We need to define variables, such as
p and q, to be arbitrary expressions. Second, we need to 
be clear that the quantities that are equal are not the 
propositions themselves but their *meanings* under all 
possible interpretations. 

We have already seen, in the last chapter, how to do this.
For example, we defined the commutative property of ∧ as
follows. In mathematical natural language we can read this
as "for any expressions, p and q, the meaning of *p ∧ q* 
is equal to that of *q ∧ p* under all interpretations." 

.. code-block:: lean

  example : 
  ∀ (p q : prop_expr) (i : prop_var → bool),
    pEval (p ∧ q) i = pEval (q ∧ p) i :=
  and_commutes  -- proof from last chapter


Another Notation
----------------

As we've seen, mathematical theories are often
augmented with concrete syntactic notations that 
make it easier for people to read and write such
mathemantics. We would typically write *3 + 4*,
for example, in lieu of *nat.add 3 4*. For that
matter, we write *3* for (succ(succ(succ zero))).
Good notations are important.

One area in our specification that could use an
improvement is where we apply the *pEval* semantic
*meaning-of* operator to a given expression. The 
standard notation for sucg a "meaning-of" operator 
is a pair of *denotation* or *Scott* brackets. 

We thus write *⟦ e ⟧* as "the meaning of *e*" and 
define this notation to desugar to *pEval e*. We 
thus  write *⟦ e ⟧ i* to mean the truth (Boolean)
value of *e* under the interpretation i. Thus, the
expression, *⟦ e ⟧ i*, desugars to  *pEval e i*,
which in turn reduces to the Boolean meaning of 
*e* under *i*. 

With this notation in hand, we'll be able to write
all of the algebraic axioms of propositional logic
in an easy to read, mathematically fairly standard
style. So let's go ahead and define this notation,
and then use it to specify the commutative property
of logical ∧ using it.
Here's the notation definition. When an operation,
such as pEval is represented by tokens on either side
of an argument, we call this an outfix notation.

.. code-block:: lean

  notation (name := pEval) ` ⟦ ` p ` ⟧ `  :=  pEval p

Variable Declarations
---------------------

It's common when specifying multiple of properties of a
given object or collection of objects to introduce the
same variables at the beginning of each definition. For
example, we started our definition of the commutative
property with *∀ (p q : prop_expr) (i : prop_var → bool)*. 
Lean allows us to avoid having to do this by declaring
such variables once, in a *section* of a specification,
and then to use them in multiple definitions without 
the need for redundant introductions. Let's see how it
works. 

.. code-block:: lean

  -- start a section
  section prop_logic_axioms
  
  -- Let p, q, r, and i be arbitrary expressions and an 
  -- interpretation
  variables (p q r : prop_expr) (i : prop_var → bool)

Now we can write expressions with these variables 
without explicitly introducing them. As an aside, in
this example, we add prime marks to the names used in
imported chapter to avoid conflicts with names used in
that file.

.. code-block:: lean

  def and_commutes' := (⟦(p ∧ q)⟧ i) = (⟦(q ∧ p)⟧ i) 
  def or_commutes' :=  ⟦(p ∧ q)⟧ i = ⟦(q ∧ p)⟧ i


Specialization of Generalizations
---------------------------------

Observe: We can *apply* these theorems
to particular objects to specalize the
generalized statement to the particular
objects.

.. code-block:: lean

  #reduce and_commutes' p q i

We can use notations not only in writing 
propositions to be proved but also in our
proof-building scripts. In addition to doing
that in what follows, we illustrate two new
elements of the Lean proof script (or tactic) 
language. First, we can sequentially compose 
tactics into larger tactics using semi-colon. 
Second we can use *repeat* to repeated apply a
tactic until it fails to apply. The result 
can be a nicely compacted proof script. 

.. code-block:: lean

  -- by unfolding definitions and case analysis 
  example : and_commutes' p q i := 
  begin
  unfold and_commutes' pEval bin_op_sem,
  cases ⟦ p ⟧ i,
  repeat { cases ⟦ q ⟧ i; repeat { apply rfl } },
  end 

Associativity
-------------

.. code-block:: lean

  def and_associative_axiom :=  ⟦(p ∧ q) ∧ r⟧ i = ⟦(p ∧ (q ∧ r))⟧ i
  def or_associative_axiom :=   ⟦(p ∨ q) ∨ r⟧ i = ⟦(p ∨ (q ∨ r))⟧ i

Distributivity
--------------

.. code-block:: lean

  def or_dist_and_axiom := ⟦p ∨ (q ∧ r)⟧ i = ⟦(p ∨ q) ∧ (p ∨ r)⟧ i
  def and_dist_or_axiom := ⟦p ∧ (q ∨ r)⟧ i = ⟦(p ∧ q) ∨ (p ∧ r)⟧ i

DeMorgan's Laws
---------------

.. code-block:: lean

  def demorgan_not_over_and_axiom := ⟦¬(p ∧ q)⟧ i = ⟦¬p ∨ ¬q⟧ i
  def demorgan_not_over_or_axiom :=  ⟦¬(p ∨ q)⟧ i = ⟦¬p ∧ ¬q⟧ i

Negation
--------

.. code-block:: lean

  def negation_elimination_axiom := ⟦¬¬p⟧ i = ⟦p⟧ i

Excluded Middle
---------------

.. code-block:: lean

  def excluded_middle_axiom := ⟦p ∨ ¬p⟧ i = ⟦⊤⟧ i   -- or just tt

No Contradiction
----------------

.. code-block:: lean

  def no_contradiction_axiom := ⟦p ∧ ¬p⟧ i = ⟦⊥⟧ i   -- or just tt

Implication
-----------

.. code-block:: lean

  def implication_axiom := ⟦(p => q)⟧ i = ⟦¬p ∨ q⟧ i  -- notation issue
  
  example : implication_axiom p q i := 
  begin
  unfold implication_axiom pEval bin_op_sem un_op_sem,
  cases ⟦ p ⟧ i; repeat { cases ⟦ q ⟧ i; repeat { apply rfl } },
  end

The next two sections give the axioms for simplifying expressions
involving ∧ and ∨. 

And Simplification
------------------

p ∧ p = p
p ∧ T = p
p ∧ F = F
p ∧ (p ∨ q) = p


Or Simplification
------------------

p ∨ p = p
p ∨ T = T
p ∨ F = p
p ∨ (p ∧ q) = p

.. code-block:: lean

  end prop_logic_axioms
  end cs6501

Homework
--------

1. Formalize the and/or simplification rules.

2. Use Lean's *theorem* command to assert,
give, and name proofs that our Lean model 
satisfies all of the algebraic axioms of 
propositional logic, as formalized above. 

Solving this problem is repetitive application 
of what we've done already in a few examples,
but it's still worth writing and running these
proofs scripts a few times to get a better feel
for the process.

3. Collaboratively refactor the "code" we've
developed into a mathematical library component
with an emphasis on good design. 

What does that even mean? Good with respect to
what criteria, deciderata, needs, objectives?

- data type definitions
- operation definitions
- notation definitions
- formal validation
- some helpful examples

