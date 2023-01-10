import logic.relation

namespace cs2120

section relations

-- Our definitions will be universe-polymorphic

universe u

-- 
variables
  {α : Sort u}
  (r : α → α → Prop)

/-
Within a section, variable declarations are
implicitly inserted into definitions that use
the variables. This mechanism allows us not to
have to repeat explicit variable declarations
in multiple definitions.
-/


-- PROPERTIES OF RELATIONS

/-
Next we quickly review our definitions of three
fundamental properties of binary relations on a
type of values, α. 
-/

-- REFLEXIVE

/-
A binary relation, r, on a type/set of object, α, 
is said to be *reflexive* if every value of that 
type (or in that set) is related to itself. It is
essential that *every* object be related to itself.
Equality is the easiest example. It is by definition
reflexive, and so whenever you need to prove x=x,
for any x, all you have to do is say "it's true by
(because of) the reflexivity of equality. In Lean,
that's "eq.refl x" or just "rfl" if Lean can infer
x.
-/
def reflexive := ∀ (a), r a a
/-
Note that this definition is equivalent to the following,
with Lean filling in the missing parts of this definition
implicitly based on the *variables* declared above. 

reflexive {α : Sort u} (r : α → α → Prop) := ∀ (a : α), r a a
-/ 


-- SYMMETRIC

/-
A relation, r, is said to be symmetric if, *whenever*
r relates two objects, a to b, it also relates b to a.
-/
def symmetric := ∀ (a b), r a b → r b a 
/-
As an example, equality is also symmetric. If a = b
then b = a for any a and b ( of the same type in Lean
and related proof assistants). This fact is not an
axiom but a theorem. That is, we don't just define
(assume) it to be true. Rather we prove it from the
axioms of equality: reflexivity and substitutability
of equals for equals. 

Proof: Suppose a = b. We are to prove b = a. By the
substitutability axiom and the fact that a = b, it
will suffice to prove a = a (because if that's true
we can replace the first a with b using the axiom
of substitutability). But a = a by the reflexivity
of equality, and so we have proved that equality is
also *symmetric*.

Another good example of a symmetric relation is the
"friend_of" relation on Facebook. If any person (as
represented by a Facebook account), x, is friends 
with any other, y, then y is necessarily also friends
with x. 

Challenge: Identify at least one other mathematical
relation that is symmetric. Then identify at least 
one other "real world" relation that is symmetric.
Briefly explain your reasoning in each case.

Challenge: If a relation, r, is empty (thus doesn't
relate any object to any other), is r symmetric or
not?

Challenge: Is Twitter's "follows" relation transitive?
Briefly explain your answer.
-/


-- TRANSITIVE

/-
Next, we say that a relation, r, is transitive, if, 
whenever r relates any objects a and b, and b and c,
it also relates a to c.
-/
def transitive := ∀ (a b c), r a b → r b c → r a c
/-
Equality is transitive. The proof is very similar to
the proof of symmetric. Here assume the premises a = b
(remember we're talking about the case where r is the
equality relation!), and b = c, and are left to prove
a = c. Use a = b to rewrite a = c to b = c, and the
rest is trivial: we've already assumed b = c, so the
goal is proved.

Challenge: If r is an *empty* relation on values of 
some type, α, (r doesn't relate any objects) then is
r transitive?

Challenge: Give an example of another mathematical 
relation that's transitive (no proof needed in this
case). 

Challenge: Is Facebook's friend relation transitive?
Briefly explain your answer.
-/


-- EQUIVALENCE RELATION

/-
Now we start to see how mathematical definitions
are built up "inductively," with big definitions
assembled from smaller ones. Here we define the 
property of a relation, r, being an "equivalence 
relation" as the conjunction of being reflexive, 
symmetric, and transitive." Our increasing fluency
with logical notations now lets us write such an 
idea with great economy and precision. 
-/
def equivalence := 
  reflexive r ∧ 
  symmetric r ∧ 
  transitive r

/-
Challenge: Formally state and prove the propositions
that equality is a reflexive, symmetric, transitive, 
and an equalivalence, relation. 
-/

theorem eq_refl : reflexive (@eq α) := 
begin
  -- expand definition of reflexive
  unfold reflexive,

  -- What's really to be proved
  show ∀ (a : α), a = a,

  -- assume a is an arbitrary value
  assume a,

  -- prove a = a "by reflexivity of eq"
  exact eq.refl a,
end


theorem eq_symmetric : symmetric (@eq α) :=
begin
  -- expand definition of symmetric
  unfold symmetric,

  -- let a and be be arbitrary values
  assume a b,

  -- assume a = b
  assume h,

  -- what remains to be shown
  show b = a,

  /- 
  It will suffice to show b = b,
  because in that case we can use
  substitutability of equals to
  rewrite the second b as a. Then
  by reflexivity the proof is done.
  -/
  rw h,
end 



theorem eq_transitive : transitive (@eq α) :=
begin
-- By the definition of transitive we are to show ...
unfold transitive,

-- We are to ...
show ∀ (a b c : α), a = b → b = c → a = c,

-- To start let a, b, and c be arbitrary values, ...
intros a b c,

-- And assume a = b and b = c
assume h_ab h_bc,

-- Now we need to show a = c
show a = c,

/-
By the substitutability of equals axiom,
we can reduce this goal to showing b = c. 
-/
rw h_ab,

/-
But that's already assumed, so the proof
is complete.
-/
assumption,
end



/-
Finally, state and prove the proposition that
equality (on the values of any type, α) is an
equivalence relation. 
-/
theorem eq_equivalence {α : Sort u} : equivalence (@eq α) :=
begin
-- By the definition of equivalence ...
unfold equivalence,

-- we are to show ...
show reflexive eq ∧ symmetric eq ∧ transitive eq,

-- By and introduction it will suffice to prove each conjunct
apply and.intro _ (and.intro _ _),
-- whoa, that's cool

/-
Each is true *by the theorems we've already proved*
-/
exact eq_refl,
exact eq_symmetric,
exact eq_transitive,
end

/-
Now we see that in mathematics not only can we build up 
complex definitions from less complex definitions, but we 
can also build up more complex proofs from less complex
ones, typically referred to as theorems or lemmas. In our
constructive logic, a theorem or a lemma is just a proof
that we've already got in hand. This lesson illustrates
the point clearly. We first prove theorems then use the
proofs to prove more complex theorems. This is really 
how mathematics works! FWIW, the Lean math library now
contains proofs of over 100,000 important theorems, in
discrete mathematics and in many other areas of maths. 
-/

end relations -- section
end cs2120    -- namespace