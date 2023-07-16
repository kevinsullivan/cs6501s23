/-

For each natural number, *a*, we will
define *le a* to the a *property* (one property for each *a*,
making a family) of being less than or equal to a second ℕ,
*b*. We then define constructors necessary and sufficient to
build proofs of *a is less or equal to than b* whenever that
is mathematically true. A *refl* constructor will produce a
proof of *a is less than or equal to a* for any *a*, and a
*step* constructor given any proof of *a ≤ b* will return
a proof of *a ≤ b + 1*. Think about it. It works.  


put these ideas together to write a function that returns 
a proof of *P a = 0 + a = a* given any natural number value, 
*a*, as an argument, and where *P* is a predicate given by
this definition. 

That function will be the proof we seek. Consider that it's
type is exactly *∀ (a : ℕ), P a* where, again, *P a := 
0 + a = a.* It asserts that for
any *a* there's a proof 0 is a left identity for that *a*.
As functions in Lean are total, we conclude 

If there's no smallest values of a type from which all 
other values are built, then no matter how small a value
you start building from, there will always be even smaller
values that you miss. Such a proof cannot be taken to be a
proof for *all* values of the type, because it isn't one. 



Smallest values are required for such a recursion to be *well
founded* and thus to terminate after a finite number of steps
for *any* argument, *a*. Proofs of universal generalizations
can be constructed for all ℕ values by induction, but not for
all integers, because the integers lacks a *well ordering,*
ending at a smallest value of the type. Clearly there is no
value in the integers smaller than any other value of this 
type.  


---

An inductive family is an *inductive type* (not a function), 
whose type is not just *Type* or *Prop* but that maps values 
of some type or types, α, β, etc. into Prop. For example, we
will represent the *less than* relation on natural numbers as
an inductive family. So let's begin. 

For each natural number, *a*, we will
define *le a* to the a *property* (one property for each *a*,
making a family) of being less than or equal to a second ℕ,
*b*. We then define constructors necessary and sufficient to
build proofs of *a is less or equal to than b* whenever that
is mathematically true. A *refl* constructor will produce a
proof of *a is less than or equal to a* for any *a*, and a
*step* constructor given any proof of *a ≤ b* will return
a proof of *a ≤ b + 1*. Think about it. It works.  


put these ideas together to write a function that returns 
a proof of *P a = 0 + a = a* given any natural number value, 
*a*, as an argument, and where *P* is a predicate given by
this definition. 

That function will be the proof we seek. Consider that it's
type is exactly *∀ (a : ℕ), P a* where, again, *P a := 
0 + a = a.* It asserts that for
any *a* there's a proof 0 is a left identity for that *a*.
As functions in Lean are total, we conclude 

If there's no smallest values of a type from which all 
other values are built, then no matter how small a value
you start building from, there will always be even smaller
values that you miss. Such a proof cannot be taken to be a
proof for *all* values of the type, because it isn't one. 




 

Smallest values are required for such a recursion to be *well
founded* and thus to terminate after a finite number of steps
for *any* argument, *a*. Proofs of universal generalizations
can be constructed for all ℕ values by induction, but not for
all integers, because the integers lacks a *well ordering,*
ending at a smallest value of the type. Clearly there is no
value in the integers smaller than any other value of this 
type.  


----

Proof by induction is a general method for constructing
proofs of universal generalizations ∀ a, P a by* building
proofs of *P a* for *larger* values of *a* from proofs of
*P a'* for one-constructor-application smaller values, a'.
This method is vitally important for proving that every 
value of a *recursive type*, α, has some property P, where
these values are themselves recursively constructed. 

An example  of a recursive type is ℕ, of course. There is 
a smallest, or *base*, value (zero), and a constructor 
(succ), that  takes a term of this type and uses it to 
build a larger term representing a next larger value of 
the same type.  Starting from base values, all values of 
the type are thus constructed.

Proofs constructed by induction have exactly this kind
of recursive structure. There are *base* (non-recursive)
proof about objects, and there are functions that step
up from given proofs about smaller objects to proofs 
about about larger objects of the same type.  

The concept of proof by induction is usually taught in
high school or college only through the special case of 
proof by induction that all *natural numbers* have a
given property. The specialization of proof by induction
to natural numbers in particular is often call proof by
*mathematical* induction.

In the next section of this chapter, we will stick with
the usual approach of introducing the general idea via
the special case of mathematical induction. In the next
chapter after, we'll see proof by induction generalizes
to all inductively defined types. It is a very general
and vital approach to proof construction, particularly
for proofs of universal generalizations over values with
recursive structures, such as nat, list, tree, or even
*program*. 

------------------


The resulting proof object has a recursive structure. 
Just as we've represented a non-zero natural number,
n as the successor of some one-smaller natural number,
n', so here we represent a proof of P for n = n' + 1
as a term that adds another layer of "proof stuff"
around a proof of P for n', ultimately terminating 
with a proof of P for 0, with further sub-structure. 

--------

/-
invalid field notation, type is not of the form (C ...) where C is a constant
  0
has type
  ?m_1
-/
lemma dud : ∀ (a : nat), 0 + a = a
↔ (0:nat).add a = a :=
begin
assume a,
split,
repeat { 
  assume h,
  apply h
},
end

-- dumb change of notation lemma only
lemma zero_ident_nat_add_notation :  
  ∀ (a : ℕ), 
    (a + 0 = a ∧ 0 + a = a) ↔ 
    (((0:nat).add a = a) ∧ (nat.add a 0 = a)) :=
begin
assume a,
split,

-- forward (Lean does simplification for us)
assume h,
cases h with r0 l0,
split,
exact l0,
exact r0,

-- backward
assume h,
cases h with l0 r0,
split,
exact r0,
exact l0,
end
-- QUOTE.




-/