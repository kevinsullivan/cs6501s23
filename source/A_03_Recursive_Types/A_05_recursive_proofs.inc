
****************
Recursive Proofs
****************

Proof by Induction
------------------

Motivation
~~~~~~~~~~

There was something notably questionable in the last
chapter. We defined a *safe* version of *fold* by requiring
a proof that the value returned for an empty list be a 
*right* (but not a *left*) identity element for the actual
binary operator parameter given to the fold function.

We then found it easy to prove that 0 is indeed a right
identity for nat.add. They key insight you need to have
is that it was easy to prove because it's already given
to us as an *axiom* by the very definition of nat.add. 
In particular, the first rule in this definition states
exactly that for any *a, nat.add a nat.zero = a*. Here's 
the definition of nat.add from Lean's core library:: 

  def add : nat → nat → nat
  | a  zero     := a
  | a  (succ b) := succ (add a b)


.. code-block:: lean

  -- and a proof
  example : ∀ (n : ℕ), nat.add n 0 = n :=
  begin
  assume n,
  simp [nat.add],
  end

An English version of this 
proof might go like this: *We're to prove 
that for any n, n + 0 = n.* Proof: Assume n
is an arbitrary but specific natural number. 
By the first rule/axiom defining nat.add we 
can rewrite n + 0 as n. That's it. As n is
general, the conjecture, n + 0 = n, is true 
for all n. 
What's *not* provided by the definition
of nat.add is an axiom that stipulates
zero is a *left* identity for nat.add.
If we try the same proof technique to
prove *∀ n, 0 + n = n*, with 0 now on
the left, we can't! (When writing these
propositions and proofs, use nat.add in
a consistent manner instead of 0. It's 
a complication that's annoying, but for
now just follow this simple instruction
and you'll be fine.)

.. code-block:: lean

  example : ∀ n, nat.add nat.zero n = n :=
  begin
  assume n,
  simp [nat.add],
  -- oops, that didn't help; we're stuck!
  end

Looking at what remains to be proved, we
might consider proof by case analysis on
n. So let's try that. 

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

The problem is that all we know about n'
is that it's some natural number, and that
isn't enough to work with to prove the goal.
That's the probem we solve now.


A Solution
~~~~~~~~~~

What if we knew a little more? What if we
knew that 0 is a left zero for n' as part
of the context in which are to prove that
it's a zero for (succ n')? Would that help?

It would. Suppose we know that *add 0 n' = n'*
and that we want to prive that *add 0 (succ n')
= (succ n')*. Key insight: We can apply the 
*second* axiom of addition,given by the second 
rule in its definition, to rewrite the term, 
*add 0 (succ n')* to the term *succ (add 0 n');*
then we can use the fact that (by assumption) 
0 is a left 0 for n' to rewrite the term 
*succ (add 0 n')* to *succ n'.* That's it. 
We've shown that 0 + succ n' = succ n'.

But what could possibly justify assuming 
that 0 + n' = n' in the first place? Well,
let's see if it can be justified informally
before getting into formalities.

Let's start by noting that by the first rule 
of addition, 0 is a left zero for 0. This
proof gives us a base on which we can now
construct a proof that 0 is a left zero for 1. 

Details: we want to show that 0 + 1 = 1. That 
is, we want to show that 0 + succ 0 = succ 0. 
By the second rule/axiom of add, the left side 
is succ (0 + 0). *BE SURE YOU UNDERSTAND THIS
STEP.*  Now by the first rule, 0 + 0 = 0, so 
we can rewrite succ (0 + 0) to just succ 0. 
With this expression on the left side, all 
thatremains to prove is that succ 0 = succ 0,
and this is true of course by the reflexivity 
of the equality relation. 

To recap, we proved a "base case" (that
zero is a left identity for zero) using the 
first axiom of addition. Then we applied the
second axiom to show that 0 is a left identity
for 1. With this proof in hand we can apply
the second axiom *again* to construct a proof
that zero is left identity for 2. From this
we can derive that 0 is a left identity for
3. Indeed to prove that 0 is a left identity
for *any* n, we start with a proof that it's 
a left identity for zero using the first
axiom, then we iteratively apply the second
axiom n times to prove it's a left identity
for *any* n. 

Let's just program it to make it all clear.
Out program will take any value n and return
a proof that 0 is a left identity for it. It
does this in the reverse order, constructing
a proof for the case where n is non-zero, i.e.,
where n = succ n' for some n', and obtaining 
a proof for n' *by recursion*. The recursive
calls implement iteration until the base case
of n = 0 is reached, at which point a proof
for that case is returned, the recursion
unwinds, and we're left with a proof that 0
is a left identity for that arbitrary n. The
existence of this function shows that we can
construct a proof of the proposition that 0
is a left identity for any n, and so it is
true *for all* n. And that's what we wanted.
QED. 

.. code-block:: lean

  -- a proof-returning function defined by cases
  -- takes any n and returns a proof of 0 + n = n
  def zero_left_ident_n : ∀ n, (nat.add 0 n = n)
  | nat.zero := by simp [nat.add] -- base case
  | (nat.succ n') :=              -- recursive case
    begin 
    simp [nat.add],               -- applies second rule and ...
                                  -- removes succ on each side
                                  -- by injectivity of constructors
                                  -- inherent in inductive definitions
    exact (zero_left_ident_n n'), -- prove result recursively 
    end 
  
  -- eyeball check of the recursive structure of these proofs!
  #reduce zero_left_ident_n 0     -- the proof term is unpretty (just eyeball it)
  #reduce zero_left_ident_n 1     -- the proof for 1 buids on the proof for 0
  #reduce zero_left_ident_n 2     -- the proof for 2 buids on the proof for 1
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

