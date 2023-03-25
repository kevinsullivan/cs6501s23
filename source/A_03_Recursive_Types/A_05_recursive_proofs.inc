
****************
Recursive Proofs
****************

This chapter you will teach you about proof by induction.

Proof by induction is a method for constructing proofs of
universal generalizations, of the form, *∀ (a : α), P a,*
where α is an arbitrary type and *P* is a predicate on (and
thus represents a property of) objects of type α.

The key idea is that such proofs are in general constructed
recursively, (1) with proofs of *P a* for *larger* values of 
*a* being constructible in some cases from proofs of *P a'* 
for  smaller values of *a*, and (2) starting from proofs of
*P a* for *smallest* values of *a*. 

The rest of this chapter will: 

- provide a concrete and pecific example of this reasoning and how we can automate it using tools we already have, concluding what is called the induction axiom for natural numbers (arguments to *P*); 
- see how the concept of an induction axiom generalizes to any inductively defined type, α; 
- introduce the concept of *inductive families* with recursive constructors; 
- introduce the idea of well founded recursion, meaning that a proof for every value of a type can be constructed starting with smallest values of the type. 
- recognize that some types have no smallest values, making proof by induction inapplicable in these cases


The Idea by Example
-------------------

In the last chapter we defined a *safe* version of *fold* 
by requiring that a proof be given as an argument: that the 
value returned for an empty list be a right identity for the 
binary operator argument. In many similar situations we will
require that a value be probably both a left and a right 
identity.

We found it easy to prove that *nat.zero* is indeed a right
identity for *nat.add*. So can't we just replicate the proof
that zero is a right identity to show that it's also a left
identity? The answer is actually no. 

The reason that it was easy to prove that zero is a right
identity is because it's already given as an *axiom,* by 
the very definition of *nat.add*. 

In particular, the first  rule in this definition states 
exactly that for any *a, nat.add a nat.zero = a*. Here's 
the definition of *nat.add* from Lean's core library. Look 
at the first case: if zero is the second (right) argument 
to add, we just return the first argument, which makes 
zero a right zero for any natural number first argument.:: 

  def add : nat → nat → nat
  | a  zero     := a
  | a  (succ b) := succ (add a b)

Here again is the proof we constructed. We assume *n* is
an arbitrary natural number. Then by the first rule of add,
*nat.add n zero* reduces to *n*, so all that remains to show
is that *n = n*. Lean automates construction of that proof
using *rfl*. 

.. code-block:: lean

  -- and a proof, zero on the right
  example : ∀ (a : ℕ), nat.add a nat.zero = a :=
  begin
  assume a,
  simp [nat.add],
  end

The *simp* tactict tries to find, and if found applies, 
rules/axioms from the definition of the listed functions: 
here from just nat.add. We could have used *rfl* instead
of *simp*, but writing the proof in this way emphasizes
that *simplification of expressions using already proven
or accepted lemmas* is a very important maneuver in many 
proofs. 

The Problem
~~~~~~~~~~~

What's *not* provided by the definition of *nat.add* is 
an axiom that stipulates that zero is a *left* identity
for nat.add. The problem is that if we try the same proof
technique to now prove *∀ n, 0 + a = a* (with zero now on
the left), it doesn't work! The definition of *nat.add* 
tells us nothing about the result when zero is added on 
the *left* to a value, *a*. Let's see what happens when
we try.

.. code-block:: lean

  example : ∀ n, nat.add nat.zero n = n :=
  begin
  assume n,
  simp [nat.add],
  -- that didn't help; we're stuck!
  end

We might instead consider proof by case analysis 
on *n*. That doesn't work either, as we see now.  

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

From basic arithmetic we know it's true that
every natural number, *a*, has the *property*
that *0 + a = a,* but it's also now clear that 
we don't yet have the tools to prove that this 
is true. In this section we'll present a new
method, *proof by induction,* that will close
this gap.

To begin, let's formally state the *property*
that we want to prove is true for every *nat*.
As we've seen before, we'll formally state the
property as a predicate, and then we'll see a
way to prove that this predicate is true for
every natural number. 

Let's define *(P a)* to be the proposition that
*0 + a = a*. Our goal will then be to show that
*∀ (a : ℕ), P a.*

.. code-block:: lean

  
  -- The property we want to prove is universal
  def P (a : ℕ) : Prop := nat.add nat.zero a = a
  
  #check P      -- nat → Prop   -- property/predicate

Let's take a different approach, starting with 
a problem instance, with zero on the left, that 
we can easily prove: namely when zero is also on
the right, because in this special case we *can*
use the first axiom/rule of addition. (Yes, we
can use rfl instead, but we're interested to see
a general approach.)

.. code-block:: lean

  theorem p0 : P 0 := 
  begin
  unfold P,         -- expand definition of P
  simp [nat.add],        -- rfl to finish off proof
  
  end

That was easy but it doesn't get us very far. We
next ask the question, from the value, 0, and our
proof of (P 0), can we construct a proof of (P 1)? 
In fact we can.

.. code-block:: lean

  theorem p1 : P 1 := 
  begin
  unfold P,
  have ih := p0,
  unfold P at ih,
  show nat.succ (nat.add nat.zero nat.zero) = 1, -- first rule of add
  rw ih,
  end

Lean provides some automation here. First it
applies the second rule of nat.add to change
the goal to (in effect) 1 + (0 + 0) = 1; then 
it (in effect) uses p0 to rewrite 0 + 0 as 0, 
then it uses the first rule to rewrite 1 + 0
as 1 (zero on the right), and finally rfl to
polish off the proof. 

From a proof that 0 is a *left* identity for 
0 can we build a proof that 0 is a left identity 
for one! So from a proof of P 1, can we now build
a proof of P 2? Yes, we can!

.. code-block:: lean

  theorem p2 : P 2  :=
  begin
  unfold P,
  have ih := p1,
  show 1 + (0 + 1) = 2, -- second rule of add
  unfold P at ih,       -- use ih, Lean automation
  end 
  
  theorem p3 : P 3  :=
  begin
  unfold P,
  have ih := p2,    -- just for clarity
  show 1 + (0 + 2) = 3,
  unfold P at ih,
  end 
  
  theorem p4 : P 4  :=
  begin
  have ih := p3,    -- just for clarity
  show 1 + (0 + 3) = 4,
  unfold P at ih,
  end 
  
  /- It looks like that from any nat, *a' : nat*, 
  and a proof of *P a'* we can prove *P (a' + 1)*.
  -/

Clearly we can't write such a proof for each value 
of *a'*. The next question is, *Can we generalize the
idea that we can *step up* from a proof of *P a'* to 
a proof of *P (a'+1)* for any value of *a'*?  That is,
can we show *∀ (a' : ℕ), P a' → P (a' + 1)? We can! 

.. code-block:: lean

  lemma step : ∀ (a' : ℕ), P a' → P (a'.succ) :=
  begin
  assume a' ih,
  unfold P at ih,
  unfold P,
  -- some tedious rewriting of notations is needed
  -- Lean confirms that these rewrites are valid
  show nat.add 0 a'.succ = a'.succ,
  -- now this simplification works
  simp [nat.add],
  -- same problem again
  show 0 + a' = a',
  /- 
  We've thus reduced the original goal to the
  goal of proving the hypothesis that we have
  already assumed (implication introduction). 
  -/
  apply ih,
  end

We don't yet have the proof of *∀ a, P a* that
we seek. What we do have are proofs, *p0 : P 0*
and *step: ∀ a', P a' → P (a'+1).* Moreover we've
just seen that if we start with *p0* and apply
*step a* times, we can construct a proof of *P a*
for any value, *a*. Of course now we can automate
that last step by writing a function that does 
just that: take any value, *a*, start with *p0*,
and apply *step a* times, and end up with a proof
of *P a*. The iterative application of *step* is
accomplished by recursion.

.. code-block:: lean

  -- formerly called pa (in class)
  def zero_left_ident_add_nat : ∀ (a : ℕ), (nat.add 0 a = a) 
  | 0 := p0
  | (nat.succ a') := (step a' (zero_left_ident_add_nat a'))

The function, zero_left_ident_add, proves ∀ a, P a! 
It's a universal generalization, so we can apply it to any 
specific value of *a* to get a proof that zero is a left 
identity for that particular *a*.  

.. code-block:: lean

  #reduce zero_left_ident_add_nat 0
  #reduce zero_left_ident_add_nat 1
  #reduce zero_left_ident_add_nat 2
  #reduce zero_left_ident_add_nat 3

Moreover, by inspecting the (semi-unreadable) proof 
terms, you can see that the proof term for each value, 
*a,* includes within it a proof term for the next smaller 
value, all the way down to the proof term for zero. Just 
as larger nat values are built from, and incorporate, 
smaller ones, down to zero, so do proofs of *P a* for
larger value of *a* build on and incorporate proofs of 
*P a'* for smaller values of *a',* all the way down to 
a proof of *P 0*. We thus construct proofs of *P a* for
any *a* inductively, just as we define the natural numbers
themselves inductively. This method is called *proof by 
induction*.

Summary: Proof by Induction
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let's pull the pieces of this story together. We started by 
specifying a property, *P a := 0 + a = 0*, of natural numbers. 
Then we then proved that *every* natural number, *a*, has this 
property: *∀ (a : ℕ), P a*. The proof relied on two lemmas and
a procedure that uses both of them.

- First, we constructed a proof *refl : P 0* (0 is a left identity for 0);
- Second, we proved *step : ∀ a', P a' → P (a' + 1) (from any natural number, *a',if *we have a proof of *P a'*, then we can derive a proof of P (a' + 1); 
- Finally these facts prove that every natural number *a* has property *P* by giving a function that constructs a proof of *P a* for any *a*;
- Key idea: apply *step* to *refl a* times (by ordinary recursion) to produce a proof of *P a*.  

For our particular definition of *P a* at least, we've thus proved this::

  *∀ (a : ℕ), 
    P 0 → 
    (∀ (a' : ℕ), P a' → P (a' + 1)) →
    P a*

If *a* is an arbitrary natural number, and if we have a 
proof, *base : P 0,* and if we also have a proof, *step : 
∀ (a' : ℕ), P a' → P (a' + 1)*, then by iteratively applying
*step* to *base* we can derive a proof of *P a*. As *a* 
was arbitrary, we've proved *∀ a, P a.* Moreover, the proofs
constructed in this way have recursive structures. 

At this point we've proved that zero is both a left and a 
right identity for the natural numbers. We can thus say that
zero is an additive identity (on the left and right) for the
natural numbers.  

.. code-block:: lean

  
  #check @nat.rec_on
  
  
  def base_fac := 1
  
  def step_fac : nat → nat → nat 
  | n' fac_n' := (n' + 1) * fac_n'
  
  def fac (n : nat) : nat :=
  begin
  apply nat.rec_on n,
  exact base_fac,
  exact step_fac,
  end
  
  def fac' : ℕ → ℕ 
  | 0 := 1
  | (nat.succ n') := (nat.succ n') * fac' n'
  
  #eval fac' 5
  
  #eval fac 5


Theorem: 0 is identity for ⟨ℕ, +⟩ 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


.. code-block:: lean

  -- We now have that zero is an *additive identity for ℕ*
  #check zero_left_ident_add_nat
  #check zero_right_ident_add_nat
  
  theorem zero_ident_add_nat : 
    ∀ (a : ℕ), 
      nat.add nat.zero a = a ∧
      nat.add a nat.zero = a :=
  begin 
  intro a,
  split,
  apply (zero_left_ident_add_nat a),
  apply (zero_right_ident_add_nat a),
  end

We've now made a major advance toward being able to formalize
our first important algebraic structure, that of a *monoid*.
In particular, we're now well along to showing that ⟨ℕ, 0, +⟩ 
is a monoid. We still have some unresolved issues to address,
however.

- To be a monoid, the given binary operator must be associative
- We'll want monoids with other binary operations, e.g., ⟨ℕ, 1, *⟩ 
- We'll want monoids over other types, e.g, ⟨list α, [], append⟩ 

Many of the proofs we'll need will rely on the induction method.
To get there, we need to understand how induction is a *general*
method of proof construction. It generalizes:

- from the property of *having 0 as an identity for +* to any property of natural numbers
- from properties involving natural number to properties involving other types (e.g., list)

The plan going forward is:

- induction axioms (recursive proof building functions) *in general*
- a proof that nat + is associative, giving us what we need for a ⟨ℕ, +, 0⟩ monoid
- proofs that 1 is a * identity, and that * associative, giving us a ⟨ℕ, *, 1⟩ monoid
- generalize to other types, with ⟨list α, append, []⟩ as a monoid on lists example 
- a final version of foldr, extending the binary operation of any monoid to n-ary 

Induction Axiom for ℕ 
~~~~~~~~~~~~~~~~~~~~~

The principle we've developed is available as an axiom 
generated from the definition of the nat data type. The
name of the principle is *nat.rec_on*. Applying it to the
smaller lemmas yeilds a proof of the generalization. 

If you prove the lemmas first, in a bottom-up proof style,
you can just apply the induction principle to a value, *a*,
and to the two proofs, to get a proof of *P a*. Or you can
apply the axiom giving only nat value as an argument while
leaving the proof arguments to be provided as proofs of 
subgoals. 

.. code-block:: lean

  -- The induction principle for natural numbers.
  #check @nat.rec_on

A top-down approach is more typical, wherein we apply the 
induction axiom for natural numbers to construct the overall
proof we need, leaving the smaller lemmas to be proved as
subgoals. 

.. code-block:: lean

  example : ∀ a, P a :=
  begin
  unfold P,
  assume a,
  apply nat.rec_on a,
  exact rfl,    -- base case
  exact step,   -- we use already proven lemma
  end
  
  -- You can also use Lean's *induction tactic*.
  example : ∀ a, P a :=
  begin
  assume a,
  unfold P,
  induction a with a' ih, -- applies axiom
  exact rfl,              -- base case
  simp [nat.add],
  assumption,
  end


Theorem: 1 is identity for ⟨ℕ, *⟩  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Here from Lean's library is the definition
of natural number multiplication. Your job 
is to prove that 1 is an identity (left and
right identity) for ⟨ℕ, *⟩. Fill in the missing proof.

.. code-block:: lean

  #check nat.mul
  /-
  def mul : nat → nat → nat
  | a 0     := 0
  | a (b+1) := (mul a b) + a
  -/
  
  theorem mul_one_ident_nat : 
      ∀ (a : ℕ), 
      (nat.mul 1 a = a) ∧
      (nat.mul a 1 = a)  :=
  begin
  assume a,
  split,
  
  -- left conjunct: nat.mul 1 a = a
  induction a with a' ih,
  -- base case
  simp [nat.mul], 
  -- inductive case
  simp [nat.mul],
  rw ih,
  
  -- right conjunct: nat.mul a 1 = a
  simp [nat.mul],
  apply zero_left_ident_add_nat,
  end


Theorems: ℕ + and * associative
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In this section we'll first construct a proof, nat_add_assoc, 
that nat.add is associative, then we'll do the same, under the
name, nat_mul_assoc, showing that nat.mul is associative, too.


.. code-block:: lean

  theorem nat_add_assoc : 
    ∀ (a b c), 
      nat.add a (nat.add b c) =
      nat.add (nat.add a b) c :=
  begin
  assume a b c,
  induction c with c' ih,
  
  -- base lemma
  simp [nat.add],
  
  -- induction lemma
  simp [nat.add],
  assumption,
  end
  
  -- Yay, that's really cool!
  
  -- EXERCISE: Prove that nat.mul is associative
  
  /-
  In the middle of trying to prove this theorem, we run into the need
  for another theorem, not yet proved: one that shows that nat add and
  mul follow the distributive law for multiplication on the left over 
  a sum. We present here an example of how one can assume a proof of a
  lemma using sorry, with the intent of filling it in later. This gives
  you a practical approach to top-down proof construction, just like 
  you might follow a discipline of top-down program construction.  
  -/
  theorem nat_mul_assoc : 
    ∀ (a b c : ℕ), nat.mul a (nat.mul b c) = nat.mul (nat.mul a b) c :=
  begin
  assume a b c,
  induction c with c' ih,
  -- base case
  simp [nat.mul],
  -- inductive case
  simp [nat.mul],
  rw <- ih,
  have mul_distrib_add_nat_left : 
    ∀ x y z, 
      nat.mul x (nat.add y z) = 
      nat.add (nat.mul x y) (nat.mul x z) := 
      sorry,
  apply mul_distrib_add_nat_left,
  end
  
  -- We leave the proof of left distributivity as an exercise (not trivial)
  lemma mul_distrib_add_nat_left : 
    ∀ x y z, 
      nat.mul x (nat.add y z) = 
      nat.add (nat.mul x y) (nat.mul x z) := sorry
  


Monoids and Foldr
~~~~~~~~~~~~~~~~~

We can now define a general structure that we can instantiate to 
formally represent either and additive or a multiplicative monoid 
on the natural numbers. Indeed, we can generalize this definition
to a monoid on values of any type for which a suitable operator and
identity element can be defined.


.. code-block:: lean

  universe u
  
  -- general structure (not we've removed "nat" from the name)
  structure monoid {α : Type} : Type := mk::
    (op : α  → α  → α )
    (id : α )
    (e : ∀ a, op id a = a ∧ op a id = a)
    (assoc: ∀ a b c, op a (op b c) = op (op a b) c)
  
  def nat_add_monoid := monoid.mk nat.add 0 zero_ident_add_nat nat_add_assoc  
  def nat_add_monoid' := monoid.mk nat.add 1 zero_ident_add_nat nat_add_assoc -- caught error
  def nat_mul_monoid := monoid.mk nat.mul 1 mul_one_ident_nat nat_mul_assoc   -- sorry 
  
  #reduce nat_add_monoid
  #reduce nat_mul_monoid
  
  -- Monoid structure instances 
  #reduce foldr nat_add_monoid.op nat_add_monoid.id [1,2,3,4,5]
  #reduce foldr nat_mul_monoid.op nat_mul_monoid.id [1,2,3,4,5]
  
  
  -- A version of foldr that takes a monoid object and uses its op and e values
  def foldr' {α : Type} : @monoid α → list α → α  
  | (monoid.mk op e _ _) l := foldr op e l
  
  -- Safe use of monoid instances folds
  #reduce foldr' nat_add_monoid [1,2,3,4,5]
  #reduce foldr' nat_mul_monoid [1,2,3,4,5]

If we ignore the fact that we don't yet have proofs of the
monoid laws for ⟨list α, [], list.append⟩ we can actually go
ahead and see that it's going to work.

.. code-block:: lean

  def monoid_list_append' {α : Type}: @monoid (list α) :=
    monoid.mk list.append [] sorry sorry 
  
  #eval foldr' monoid_list_append' [[1,2,3],[4,5,6],[7,8,9]]

All that remains is to provide the requisite proofs that 
append and nil satisfy the *monoid laws*. Unlike the proofs
of identities and associativity for natural number operations,
however, we now need to show that [] is an identity for *list*
append and that append is associative. If proof by induction 
worked as well for lists as for natural numbers we'd be all
set. As we'll see next, we're in luck. 

Induction Axioms
----------------

In this chapter, we will meet the idea that there is
an induction axiom for *every* inductive definition. 
We'll start by showing that our reasoning about 0
being an identity for nat.add extends directly to
showing that [] is an identity (left and right) for
list.append. We'll then discuss the general case.

Theorem: [] list append identity  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Our overall aim is to show that ⟨list α, [], ++⟩ is
a monoid. Then we'll be able to use foldr to extend
++ to an operation that will append any number of
lists as long as they are themselves arranged in a
list of lists. 

We therefore need to show that [] is an identity on
the left and right for append (++), and that append
is associative. Let's take the first theorem here:
[] is an identity for ++. 

.. code-block:: lean

  -- To be proved
  theorem nil_identity_append_list {α : Type u}: 
    ∀ (l : list α), 
      list.append list.nil l = l ∧ 
      list.append l list.nil = l := sorry
  
  -- Here again is the definition list.append (++). 
  #check @list.append
  /-
  def append : list α → list α → list α
  | []       l := l
  | (h :: s) t := h :: (append s t)
  -/

By definition, list.nil is a left identity, but as
with nat.add, there's no rule telling us that [] is
a right identity. It thus appears (and is the case)
that we will have to prove that [] is an identity on
the right by induction.

Let's think about what the induction will look like.
It will be induction on the left argument to append.
First we'll need a proof that [] is a right identity
for [] on the left. Then we'll need to show that *if*
for any list, l' on the left, [] is a right identity
for l' then it's a right identity for any one-larger
list. Such a one-larger list can be any list, hd::l', 
where hd could be any element of type α. 

Let's start with a bottom-up approach. We'll begin
by formally defining the *property* of lists that
we want to show is universal, that [] is a right
identity for any list, l.

.. code-block:: lean

  def list_nil_right_ident_for {α : Type u} (l : list α) :=
    list.append l [] = l
  
  
  lemma list_base {α : Type u} : 
    list_nil_right_ident_for ([] : list α) :=
  begin
  -- unfold list_nil_right_ident_for,
  exact rfl,  -- Lean unfolds name automatically here
  end
  
  -- Now let's prove a step lemma.
  #check @list.rec_on
  
  lemma list_step {α : Type u} : 
    -- given any new head element, hd
    (Π (hd : α) 
    -- and any existing list, l'
       (l' : list α), 
    -- if [] is a right identity for l'
       list_nil_right_ident_for l' → 
    -- then it's a right identity for one-bigger list
       list_nil_right_ident_for (hd :: l')) :=
  begin
  unfold list_nil_right_ident_for,
  assume hd l' ih,
  simp [list.append], -- simplify using second rule of append
  assumption,         -- the induction hypothesis finishes it off QED
  end 
  
  -- Now we build a recursive function to return proof for any l
  #check list_base
  
  def nil_right_ident_append_list' {α : Type} : ∀ (l' : list α), list.append l' [] = l'
  | (list.nil) := list_base
  | (h::t) := list_step h t (nil_right_ident_append_list' t)
  
  -- Seems to work!
  #check nil_right_ident_append_list' [1,2]
  


Induction Axiom for Lists
~~~~~~~~~~~~~~~~~~~~~~~~~

We see again that there's nothing myseterious about proof by induction.
If we have base values/proofs and step functions to build next-bigger 
ones, and we can have a function that (using recursion on these elements)
computes a value/proof for any given input value, and thus for all values
of the input type. 

Proof by induction is done by functions that compute results using
recursion on given base values and step functions.  Every inductive
axiom can be understood as a proof of universal generalization that
asserts that every value of some input type has a corresponging result
value of type. These return values can be proofs of properties or they
can be function return values of any type. 

Let's look at and compare and contrast the induction axioms (they're 
just higher order functions!) for the nat and list α types. We'll then 
show how the same ideas developed in the last example apply directly 
as well to induction on list values. 

.. code-block:: lean

  #check @list.rec_on
  /-
  nat.rec_on :                    
    Π {motive : ℕ → Sort u_1}   -- property or return value type
      (n : ℕ),                  -- input argument value
      motive 0 →                -- answer for base case
      (Π ('n : ℕ),              -- step function (higher-order!)
        motive n' → 
        motive n'.succ
      ) → 
    motive n                    -- return values, by recursion
  -/
  
  #check @list.rec_on
  /-
  list.rec_on :
    Π {T : Type u_2}                -- for any list element type
      {motive : list T → Sort u_1}  -- property or return type
      (n : list T),                 -- input argument value  
      motive list.nil →             -- proof/value for base case
      (Π (hd : T)                   -- step function: understand it
         (tl : list T), 
         motive tl → 
         motive (hd :: tl)) → 
    motive n                        -- return value, by recursion
  
  
  QUESTION: What new element is present in the rule for lists
  that isn't involved in the rule for natural numbers?

Once again we'll have to show *[]* is both a left and 
right identity for append, where one proof is by the 
definition of append and the other is by induction. We'll 
also need a proof that *list.append* is associative: 
*∀ (l m n : list α), (l ++ m) ++ n = l ++ (m ++ n).  

Here's the definition of list.append.
You can see it defines [] as a left identity for any list. 

.. code-block:: lean

  /-
  def append : list α → list α → list α
  | []       l := l
  | (h :: s) t := h :: (append s t)
  -/
  
  
  theorem nil_left_ident_append_list (α : Type) : ∀ (l : list α), list.nil ++ l = l :=
  begin
  assume l,
  simp [list.append],
  end

We run into the same problem as we did before if we take a
naive approach to trying to prove that nil is also a left
identity for ++. And the solution is once again to define
a recursive function by case analysis on l that constructs
a proof of *nil ++ l = l* for any list l. If l = list.nil,
the proof of nil ++ nil is given by the first rule of list
append, otherwise l = (h::t), and we need to prove that
nil ++ h::t = h::t. By the second axiom of list append,
we can rewrite nil ++ h::t as h::(nil ++ t), where we can
obtain (and then us) a proof that nil ++ t = t by recursion,
terminating when t =nil. 

.. code-block:: lean

  def nil_right_ident_append (α : Type) : 
    ∀ (l : list α), l ++ [] = l :=
  begin
  assume l,
  induction l,
  simp [list.append],
  simp,
  end


Theorem: monoid (list α)
~~~~~~~~~~~~~~~~~~~~~~~~

The work you've done until now should have you prepared to finish off
the definition of a monoid instance for list α, [], list.append. You need
the following:

- a proof that list.append is associative
- to package up the elements you now have into a finished monoid instance
- tests passing this monoid to foldr to see it doing the right things

This is your homework. You should try it by yourself, for sure, and put strong
effort into solving it. If you end up fruitlessly stuck, you may go ahead and
talk to others, but take the minimal input needed to get unstuck. Maximize your
learning and understanding.


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

