
import logic.relation

namespace hidden 

/- Equality Propositions and Equality Relations

We will now shift focus to the specific binary 
relation on any type, α, that we call equality.
Equality in Lean is polymorphic: Given any type
(in any type universe), we have a binary relation 
on values of that type, of type α → α → Prop.
-/

-- Let's inspect the type of eq
#check @eq
-- eq : Π {α : Sort u_1}, α → α → Prop
-- infix ` = `:50 := eq

/-
In English, given any (Π) type, α, eq
takes two values of this type and reduces
to the proposition that these two values
are equal. So eq x y is the proposition,
x = y, and in fact Lean provides = as an
infix notation: the one you're accustomed
to from school days.
-/

-- These expressions mean the same thing
#check eq 0 0
#check 0 = 0


/- PROOFS 

Up until now, all we've talked about is a mechanism,
eq, for generating propositions. What are the rules 
for constructing and using proofs of equality? 
-/

/- Inference rules

Equality has two inference rules: an introduction rule, 
eq.refl, and an elimination rule, eq.subst. All other 
properties of equality come from these two rules and 
the meaning of "inductive definitions" in Lean (as we'll 
see in a bit). 
-/

/- Introduction rule: eq.refl

The introduction rule establishes the fact (constructs
proofs) that every object of any given type is equal to
itself.
-/

#check @eq.refl
-- ∀ {α : Sort u} (a : α), eq a a

#check eq.refl 0
-- eq 0 0, i.e., proof of 0 = 0

example : 0 = 0 := eq.refl 0

-- When Lean can infer "a" you can use rfl.
example : 0 = 0 := rfl

#check @rfl
-- ∀ {α : Sort u_1} {a : α}, a = a

/-
Note: in our logic you can't form a proposition that 
two things of different types are equal. It's just a 
type error, given the definition of eq.
-/

#check tt = "hi"    -- type error


/- Elimination rule: eq.subst

The second axiom of equality defines its elimination 
rule: that is, how we can *use* a proof of an equality.
If you have a predicate, P : α → Prop, for some type, 
α, and if you know P a, and you know a = b, then you
can deduce P b.

For example Tom is from New York (FromNY Tom), and 
Bob = Tom, the by eq.subst you can deduce FromNY Bob. 
Here's the rule formally.
-/

#check @eq.subst
/- eq.subst : 
  ∀ {α : Sort u_1} 
  {P : α → Prop} 
  {a b : α}, 
  a = b →           -- if you know a = b
  P a →             -- and if you know P a
  P b               -- you can deduce P b
-- in reverse, 
-- to show P b 
-- suffices P a and a = b
-/

/-
What this rule really says is that if you 
have a goal, P b, and you know a = b, you
can rewrite the goal as P a and the result
will be equivalent.

The following example sets up the use of 
eq.subst. There are balls, balls can be 
blue, a and b are balls, a is b, and a is
blue. The goal is to show that b is Blue.
That is done by applying eq.subst to the
proof of equality of a and b, and to the
proof that a is Blue. 
-/

example 
  (Ball : Type)
  (Blue : Ball → Prop)
  (a b : Ball)
  (eq_balls : a = b)
  (a_is_Blue : Blue a) :
  Blue b := 
eq.subst eq_balls a_is_Blue

/-
This next example show that applying
eq.subst to a proof of a = b reduces
the goal of showing Blue b to that of
showing Blue a. In a sense, applying 
eq.subst to an equality proof effects
a *rewriting* of the current goal. 
-/
example 
  (Ball : Type)
  (Blue : Ball → Prop)
  (a b : Ball)
  (eq_balls : a = b)
  (a_is_Blue : Blue a) :
  Blue b :=
begin
  -- Study the sequents before and after this step
  apply eq.subst eq_balls,
  assumption,  -- now we can use *this* proof!
end

/-
Lean provides a useful tactic called
rewrite that automates application of
eq.subst to effect such rewritings. The
following two example illustate use of
two different forms of the tactic. In
short, given h : a = b, "rw h" changes
a's in the goal to b's and rw<-h changes
b's in the goal to a's.
-/

example 
  (Ball : Type)
  (Blue : Ball → Prop)
  (a b : Ball)
  (eq_balls : a = b)
  (a_is_Blue : Blue a) :
  Blue b := 
begin
rw<-eq_balls, -- rewrite b to a (right to left)
assumption,
end


-- Exercise: complete the proof
example (α : Type) (a b : α) (P : α → Prop) : a = b → P b → P a :=
begin
intros ab Pb,
rw ab,
assumption,
end


/- Properties of The Equality Relation -/

/- Reflexivity 

In English you can say a relation, r, is reflexive 
if it relates *every* value, x in its "domain" to x 
itself: that is ∀ x, r x x. Remember the relation r 
is specified by a two-place predicate. So ∀ x, r x x 
says that *every* value, x, is related to itself by r.    
-/

#check @reflexive
/-
reflexive : Π {β : Sort v}, (β → β → Prop) → Prop

Π (capital Pi) means universal quantification. So, 
what reflexive says is that "for any type, β (even 
a propositional type), reflexive defines a property 
of any binary relation on β. 

Put another way, if you apply reflexive to any binary 
relation on any type, β (inferred), you will get a 
proposition: the one that precisely expresses what 
it means for such a relation to be reflexive: that 
every element of the domain is related to itself *in 
that relation*.  

For example, the reflexive predicate applied to the 
equality relation yields the proposition that every
value of a given type is related to itself by equality
in this relation.
-/

#reduce reflexive (@eq nat)

/- 
Of course, the introduction rule, refl, for equality
*makes* the equality relation reflexive. It's reflexive
by definition and so should be easy to prove.
-/

example : ∀ (X : Type), reflexive (@eq X) :=
begin
assume X,
unfold reflexive,
/- First axiom of equality: 
   X : Type ⊢ ∀ (x : X), x = x
-/
assume x,
-- all the following are equivalent
-- exact @eq.refl X x,  -- no arguments inferred
-- exact eq.refl x,     -- one argument inferred
exact rfl,              -- both arguments inferred
end

/-
Congratulations, you have earned another sticker: 
this one to recognize that you are now working with
properties of relations that in turn express 
properties of sets of ordered pairs of values. 
That's sorta cool!
-/

/- Symetric -/

/-
A relation is said to be symmetric if whenever
any object a is related to some object b, then b
is also related to a. The "friends" relation on
Facebook is symmetric in this sense. 
-/

#check @symmetric
-- Π {β : Sort u_1}, (β → β → Prop) → Prop
#reduce @symmetric
-- ∀ ⦃x y : β⦄, x = y → y = x

/-
There's the generalized, formal definition: if x and
y are values (here of type nat), then if r x y then
r y x. If r is eq, then this says if x = y then y = x.
-/

#check @symmetric
#reduce @symmetric 

/-
Exercise: prove that = is symmetric. And
answer the question, is ≤ symmetric, and
give a brief defense of your answer. If 
your answer is no, provide a counter-example
to show that you are correct.
-/

example (α : Type): symmetric (@eq α) :=
begin
unfold symmetric,
assume x y e,
rw e,
end 

example (α : Type) : transitive (@eq α) :=
begin
unfold transitive,
assume x y z xy yz,
rw <- yz,
assumption,
end 


end hidden
