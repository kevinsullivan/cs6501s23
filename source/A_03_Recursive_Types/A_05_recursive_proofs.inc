
****************
Recursive Proofs
****************

Proof by Induction
------------------

Motivation
~~~~~~~~~~

In the middle of the last chapter. We defined a *safe* 
version of *fold*  by requiring a proof that the value 
returned for an empty list be a *right* identity element 
for the actual binary operator argument given to the fold 
function: that *∀ n, n + 0 = n.* 

We also aws that it's easy to construct such a proof. The
key insight is that it's given as an *axiom* of addition. 
In particular, the first rule in the recursive definition
of nat.add makes it so. Here's the definition from Lean's
core library. 

.. code-block:: lean

  def add : nat → nat → nat
  | a  zero     := a
  | a  (succ b) := succ (add a b)

Look at the first rule: it stipulates that any value,
*a*, added to zero is equal to a. This rule establishes that 
zero is a right identity for add.  Here again is our earlier
statement and proof.  

.. code-block:: lean

  example : ∀ (n : ℕ), nat.add n 0 = n :=
  begin
  assume n,
  simp [nat.add],
  end

Note that the *simp* tactict tries to find, and if 
found applies, rules/axioms from the definition of 
any of the listed functions: here from just nat.add.

A natural language version of this proof might go
like this: *We're to prove that for any n, n + 0 = n.* 
Proof: By the definition of addition. QED. 
What's *not* provided by the definition of nat.add is 
an axiom that stipulates that zero is a *left* identity
for nat.add. To show that zero is *an identity* we need
to show that both *∀ a, a + 0 = a* and *0 + a = a*.

The problem is that if we try the same proof technique to
prove *∀ n, 0 + a = a*, with zero now on the left, it doesn't 
work. The definition of addition tells us nothing direclty
about the result when zero is added on the left to a value,
*a*. 

.. code-block:: lean

  example : ∀ n, nat.add nat.zero n = n :=
  begin
  assume n,
  simp [nat.add],
  -- oops, that didn't help; we're stuck!
  end

We might consider proof by case analysis on
n, but that doesn't work  So let's try that. 

.. code-block:: lean

  example : ∀ n, nat.add nat.zero n = n :=
  begin
  assume n,
  cases n with n',
  -- first case: zero's also on the right
  simp [nat.add],
  -- second case, argument is succ of some n'
  -- how to show 0 + (succ n') = (succ n')
  -- but again we're stuck
  simp [nat.add],
  -- basically back where we started; stuck.
  end

A Solution
~~~~~~~~~~

Let's take a different approach, starting with 
a problem instance, with zero on the left, that 
we can easily prove: namely when zero is also on
the right, because in this special case we *can*
use the first axiom/rule of addition. (Yes, we
can use rfl instead, but we're interested to see
a general approach.)

.. code-block:: lean

  theorem zero_left_id_zero : nat.zero + nat.zero = nat.zero := 
  begin
  simp [nat.add],
  end

That was easy. Now the question is whether, with 
this proof in hand, we can now construct a proof 
that 0 + 1 = 1, with zero on the left? We can of 
course prove this using rfl, but we can't use this
method to prove that 0 + a = a *for all a*, even 
in principle, because there's an infinite number
of natural numbers.  

So let's see if we can find a method that has the
potential to generalize to all nat values. Here's 
the idea: If we can construct a proof for *a = 1* 
(i.e., that 0 + 1 = 1) *from a proof for a = 0*, 
which we already have, then maybe we can make this
method generalize. Let's see a formal proof then
discuss is.

.. code-block:: lean

  theorem zero_left_id_one : 0 + 1 = 1 := 
  begin
  /-
  Key idea: use *second* add axiom to rewrite 
  add 0 (succ 0) to succ (0 + 0). Please be very
  sure you understand this point. The new goal
  to prove is thus as follows: 
  -/ 
  show 1 + (0 + 0) = 1,  
  /-
  And now, the second key idea: We can use the
  proof we already have to rewrite 0 + 0 as 0,
  and at that point Lean sees that the proof can
  be finished by applying rfl. 
  -/
  rw zero_left_id_zero,
  /-
  We have thus constructed a proof of 0 + 1 = 1
  from a proof of 0 + 0 = 0. Can we do it again
  to get a proof for *a = 2*? Yes, we can.
  -/
  end  
  
  theorem zero_left_id_two : 0 + 2 = 2 :=
  begin
  -- apply second rule of addition
  show 1 + (1 + 0) = 2,
  -- apply proof already constructed for *a = 1*
  rewrite zero_left_id_one,
  end 

Our approach of building a proof for *(a + 1)*
from a proof for *a* looks good, but clearly we
can't give such a derivation for each value of
*a*! Can we generalize over all possible values
of *a*? 

We can, actually, and that's the idea of proof 
by induction. If we have a base proof to start
with, and from it we can always build a proof
for the next value of *a*, then by iterating
that *step* operation (as we did in the examples
above) then we can build a proof for any *a.*
To do this we start with the base proof then 
iterate the *step* construction *a* times. So
let's see if we can formalize what we mean by
the *step* operation. 

.. code-block:: lean

  def left_id_step (a' : ℕ) : 
    nat.add 0 a' = a' → 
    nat.add 0 (a'.succ) = (a'.succ) :=
    begin
    assume induction_hypothesis,
    simp [nat.add],   -- by second rule for add
    assumption,       -- by induction hypothesis
    end
  


So now we have two proofs: (1) 0 is a left 
identity for 0; (2) *if* 0 is a left identity
for any natural number, *a'*, then it's also
a left identity for *a = a' + 1*. 

Putting the two proofs together is certainly 
enough us to prove that 0 is also a left identity
for 1. That in turn should be enough to prove 0 
is a left identity for one. From that proof it'd
be possible to show it's a left identity for 2.
And this process can be iterated to show, in a
*finite* number of steps, it's a left identity 
for *any* given natural number value, *a*. And
*that* finally is enough to deduce that 0 is a
left identity for *all* natural numbers. 

We can prove this reasoning is correct with a 
function that takes any natural number, *a*, 
and that returns a proof that zero is a left 
identity for that particular *a.* Let's do it.
The construction is by case analysis on *a* and
the use of recursion to interate the *step* 
operation *a* times, with the proof for 0 as
the correct proof in the case of *a = 0*.  

.. code-block:: lean

  def zero_left_ident_any_a : ∀ (a : ℕ), (nat.add 0 a = a) 
  | 0 := zero_left_id_zero
  | (nat.succ a') := (left_id_step a' (zero_left_ident_any_a a'))
  
  #check zero_left_ident_any_a

With this universal generalization in hand, we can apply it
to any particular value of *a* to get a proof that zero is a
left identity for that particular *a*. Moreover, if we look
at the proof terms being constructed, it's clear, even without
looking at the details, that a proof for *a' + 1* incorporates
(is built from) a proof for *a'*.

.. code-block:: lean

  -- eyeball check of the recursive structure of these proofs!
  #reduce zero_left_ident_any_a 0     -- the proof term is unpretty (just eyeball it)
  #reduce zero_left_ident_any_a 1     -- the proof for 1 buids on the proof for 0
  #reduce zero_left_ident_any_a 2     -- the proof for 2 buids on the proof for 1
                                  -- and we see we can build such a proof for any n
                                  -- therefore 0 is a left identity for addition

To sum up, what we've shown is that if we have two 
*little machines* we can construct a proof of the 
given proposition, let's call it P := (0 + n = n), 
for any value, n. The first machine produces a proof 
of P for the case where n = 0. The second machine, 
given a proof of P for any n' returns a proof for 
n' + 1. We've show that this is always possible. To 
construct a proof for any n, we then use the first
machine to get a proof for 0, then we run the second
machine n times starting on the proof for 0 to build
a proof for n. 

The resulting proof object has a recursive structure. 
Just as we've represented a non-zero natural number,
n as the successor of some one-smaller natural number,
n', so here we represent a proof of P for n = n' + 1
as a term that adds another layer of "proof stuff"
around a proof of P for n', ultimately terminating 
with a proof of P for 0, with further sub-structure. 
apply
Generalizing
~~~~~~~~~~~~

Just as we will need a proof that 0 is not only a right
identity for nat.add (by the first axiom) but also a left
identity (a theorem proved by induction), so will need a
proof that nil is not only a right but also a left identity
for the list append operation.  

Here's the easy case first. From this proof you can infer
that the list.append operation (with infix notation ++) has
a rule/axiom that states that l ++ nil := l for any l. 

.. code-block:: lean

  
  /- 
  Here's the definition of list.append.
  It asserts that [] is a left identity axiomatically. 
  
  def append : list α → list α → list α
  | []       l := l
  | (h :: s) t := h :: (append s t)
  -/
  
  -- proving right identity is trivial just as for addition
  example (α : Type) : ∀ (l : list α), list.nil ++ l = l :=
  begin
  assume l,
  simp [list.append],
  end


.. code-block:: lean

  def nil_left_ident_app (α : Type) : ∀ (l : list α), l ++ list.nil = l :=
  begin
  assume l,
  cases l with h t,
  -- base case
  simp [list.append],   -- uses first rule
  -- recursive case
  simp [list.append],   -- why does this work?
  end 
  
  -- Here's another formal demonstration of the same point
  variables (α : Type) (a : α) (l : list α) 
  example: list.nil ++ l = l := by simp    -- first rule
  example : l ++ list.nil  = l := by simp  -- by [simp] lemma in Lean library


Induction Axioms
----------------


Inductive Families
------------------

Coming soon.

.. code-block:: lean

  inductive le (n : nat): nat → Prop 
  -- n is an implicit firt argument to each constructor
  | refl : le /-n-/ n     
  | step : ∀ m, le /-n-/ m → le /-n-/ m.succ
  
  -- you can see it in the types of the constructors
  #check @le.refl
  #check @le.step
  
  
  example : le 0 0 :=
  begin
  apply le.refl,
  end 
  
  example : le 3 3 :=
  begin
  apply le.refl,
  end 
  
  example : le 0 1 :=
  begin
  apply le.step,
  apply le.refl,
  end 
  
  example : le 0 3 :=
  begin
  apply le.step,
  apply le.step,
  apply le.step,
  apply le.refl,
  end 
  
  -- here's the same example using Lean's version of "le"
  -- it's called nat.less_than_or_equal
  example : 0 ≤ 3 :=
  begin
  apply nat.less_than_or_equal.step,
  apply nat.less_than_or_equal.step,
  apply nat.less_than_or_equal.step,
  -- apply nat.less_than_or_equal.step,
  apply nat.less_than_or_equal.refl,
  end 
  
  -- repeat tactical goes too far; use iterate instead
  example : 1 ≤ 4 :=
  begin
  -- repeat {apply nat.less_than_or_equal.step},
  iterate 3 {apply nat.less_than_or_equal.step},
  apply nat.less_than_or_equal.refl,
  end 

