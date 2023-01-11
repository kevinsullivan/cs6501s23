import data.set

/-
Review: You've already met the relation that takes any 
natural number, n, and yields a proposition asserting 
it's even, (isEven n).
-/

def isEven (n : ℕ) : Prop := n%2 = 0

/-
You've already met the idea that this predicate 
literally represents the set of even natural numbers:
the set of all and any natural number, n, that satisfies 
the condition, n%2 = 0. That's a good basic definition
of the property of evenness of a natural number. 
-/

/- *** set comprehension notation *** -/

/-
What we add now is a notation for specifying sets of 
objects having specified properties: set comprehension 
notation. As an example, we will specify the set of all
even numbers. 

Have formalized the isEven predicate, we can now express 
this set using *set comprehension notation*. 
-/

def evens : set ℕ := { n : ℕ | isEven n }

/-
In an English language, or typeset proof, you'd say, 
"let 'evens' be the set of LL natural numbers, n, of 
type ℕ, such that n is even." Lean can infer from isEven
that the type of n has to be ℕ, and from that that the
set must have "elements" of type ℕ; so you can shorten
the definition if you wish.
-/

def evens' := { n | isEven n }


/- *** the big trick #for reasoning about sets *** -/

/-
The "big trick" in this class for reasoning about "sets" is
to remember that set comprehension notation is just notation
for the set memberships predicate, itself: here "evens" means
exactly isEven, which in turn is the predicate that takes a
natural number, n, and reduces to the proposition, n%2 = 0.
Remember that sets in Lean are not just defined using, but 
are literally equivalent to their "membership" predicates.
-/


/-
First, let's use check and eval to see that a set in our
logic is defined by, and is tantamount to, its membership
predicate.
-/
#check evens      -- set ℕ, looks like a "set" 
#check isEven     -- ℕ → Prop, looks like a "predicate"
                  -- yes, the types *look* different, but ...


-- ... they mean the same thing: it's the isEven predicate!
#reduce isEven    -- λ (n : ℕ), 2.mod_core n n = 0
#reduce evens     -- λ (n : ℕ), 2.mod_core n n = 0

/-
Don't worry, "λ (n : ℕ), 2.mod_core n n = 0" is the
function (predicate!) that takes a natural number, n, 
and returns the proposition, n%2 = 0. In other words, 
the *set*, evens, means exactly the same thing as its 
*membership predicate*, isEven.
-/


/-
Among other things, this means that you can *apply* the
"set" symbol, "evens" to an argument, such as 4, to get the 
proposition that that value, 4, mod two, equals zero, which
Lean reduces to 0 = 0. When such a proposition is true (has 
a proof, as it does here, by rfl), that proves that that
value, here 4, satisfies the membership predicate and so is 
"in" the set.
-/

#reduce evens 4   -- true by rfl, so 4 is "in" the evens set
#reduce evens 5   -- an impossibility, so 5 is not in evens


/- *** You have a new mathematical superpower! *** -/

/-
Now you have just acquired a new mathematical superpower:
the ability to precisely and abstractly define particular
sets of objects: just write the predicate that is true for 
all and only the elements of the set of interest, and then
use set comprehension notation to specify the set as a good
mathematician would. 
-/

/-
Here, for example, is a specification of the set of *all* 
string values of length 5.
-/

def strings5 := { s : string | s.length = 5 }

/-
Can we prove that some string, say "Lean!", is in this
set? Remember the big mental trick: Because the "set", 
string5, is tantamount to the *predicate*, strings5, 
that takes a string, s, and returns the proposition 
that s.length = 5, we can apply strings5 to "Lean!" to
form proposition that that (1) "Lean!" satisfies the
strings5 predicate, and so "Lean!" is in the set of 
strings that it specifies. You have in a few simple
symbols thus defined the set of *all* length-5 strings! 
-/

-- Example: Formally prove that "Lean!" satisfies strings5
example : strings5 "Lean!" := 
begin                     -- strings5 "Lean!"
unfold strings5,          -- {s : string | s.length = 5} "Lean!"
show "Lean!".length = 5,  -- identical meaning
apply rfl,                -- equality proof checks good
end

-- Example: Try and fail to prove that "Huzzoo!" is in this set
example : strings5 "Huzzoo!" := 
begin                        -- strings5 "Lean!"
unfold strings5,             -- {s : string | s.length = 5} "Lean!"
show "Huzzoo!".length = 5,   -- identical meaning
apply rfl,                   -- equality proof check fails
end

-- Example: Prove that "Huzzoo!" is *not* in this set
example : ¬strings5 "Huzzoo!"  := 
begin
assume h,                   -- proof by negation
unfold strings5 at h,       -- expand definition of term
-- Notice the notation now: a set (predicate) "applied" to a value
-- Now "Huzzoo!".length reduces to 7, so we've assumed 7 = 5 
cases h,    -- And that's an impossibility
-- So ¬strings5 "Huzzoo!" is true, by negation
end

/- *** set membership notations: ∈, ∉ *** -/

/-
Now we introduce another beautiful new notation: meet ∈, 
which we pronounce "is in." For example, we'd pronounce
"Lean!" ∈ strings5 as "the string, Lean!, is in the set,
strings5." 
  
So now instead of a predicate application, strings5 "Lean!", 
we write  "Lean!" ∈ strings5. This is the standard notation
that mathematicians write to assert that a value is in a set:
that it satisfies its membership predicate. We now restate
the preceding propositions using set membership notation. 
You should not stop studying this file until it's clear in 
your mind that "Lean!" ∈ strings5 is simply the proposition
you get by applying the predicate, λ s, s.length = 5, to the
string "Lean!" And propositions are things we can try to prove.
-/

-- Example: Prove "Lean!" is in the set of length-5 strings
example : "Lean!" ∈ strings5 := 
begin                           -- "Lean!" ∈ strings5 
unfold strings5,                -- "Lean!" ∈ {s : string | s.length = 5}
show {s : string | s.length = 5} "Lean!", -- means exactly this!
show "Lean!".length = 5,                  -- means exactly this!
show (5 = 5),                             -- means exactly this!  
apply rfl,                      -- with an easy proof by rfl
end
/-
The "show" tactic rewrites your goal into any form that is
*equal by definition* to the current one. Lean won't let you
rewrite your goal to any arbitrary form, of course.
-/

-- Example: Same proof, skipping all the nice rewriting
example : "Lean!" ∈ strings5 := 
begin
exact rfl,
end 


-- Example: Try and fail to prove that "Huzzoo!" ∈ strings5 
example : "Huzzoo!" ∈ strings5 := 
begin
exact rfl,
end
/-
Here we skip all the rewriting and just cut to the chase
-/


-- Formally prove: "Huzzoo!" ∉ (is *not in*) strings5
example : "Huzzoo!" ∉ strings5 := 
begin
show ¬(strings5 "Huzzoo!"), -- equivalent
assume h,                   -- proof by negation
unfold strings5 at h,       -- expand definition of term
                            -- h is asserting that 7 = 5!
cases h,                    -- an impossibility
-- QED, by negation
end

/- *** visualizing sets *** -/

/-
We can visualize a set as the collection of objects
that satisfy the membership predicate. We will often
draw a set as a collection of objects within a circle,
cloud, or other bounding line. The idea is that all the
objects inside the boundary are "in" the set and all 
the other objects are outside the set. [See drawing.]
-/

/-
Exercises:

What predicate is true of the elements of a set
of natural numbers containing exactly the numbers,
1, 3, and 5? Answer by completing the definition of
the following predicate.   
-/

def set135 := { n : ℕ | n = 1 ∨ n = 3 ∨ n = 5 }
-- Remember: This is a predicate with argument n
-- Predict what you get when you apply it to 5, then check
#reduce set135 5

/-
Now let's prove a few things, starting with the proposition
that the value 5 is "in" this set.
-/

example : 5 ∈ set135 :=
begin
-- applying set135 to 5 yields 5 = 1 ∨ 5 = 3 ∨ 5 = 5
show 5 = 1 ∨ 5 = 3 ∨ 5 = 5, -- which has a proof, to wit:
-- we can prove the right hand side, so let's go
right,    -- new Lean tactic: shorthand for apply or.elim_right
right,    -- new Lean tactic: shorthand apply or.elim_right
exact rfl,-- trivially true by the reflexivity of equality
end
/-
Notice how we used right (and in general will use both
left and right) to navigate through a big disjunction to
pick a disjunct that we can prove. In English you could 
just say, the disjunction is true as the disjunct ,5 = 5, 
is true. 
-/


/-
Not only can we prove that 5 is "in" the set,
{ 1, 3, 5 }, which is to say that 5 satisfies
the membership predicate; we can also prove 4
is not in the set, denoted 4 ∉ set135. That is,
the membership predicate, set135 applied to 4,
yields a proposition that is false.
-/
example : 4 ∉ set135 :=       -- "not in" notation
begin 
assume h, -- proof by negation, assume premise
cases h,  -- prove rest by repeated case analysis
cases h,  -- elim left: 4 = 1 is impossible
cases h,  -- elim right: 4 = 3 ∨ 4 = 5 impossible  
  cases h,  -- left:  4 = 3 is impossible
  cases h,  -- right: 4 = 5 is impossible
end

/- 
A little bit more Lean, optional. A "tactical"
is a tactic that takes another tactic as an
argument and does something with it. The "repeat"
tactical takes any tactic and repeatedly runs it
repeatedly until it fails. As an example, we can
use the repeat tactical to shorten the preceding 
proof script.
-/
example : 4 ∉ set135 :=
begin
assume h,
repeat { cases h, }
end

/-
So now that we have ourselves a polymorphic type,
set T, where T is any type of object, we can start
to talk about operations involving objects of this
type. (Yes, after all, they are predicates, but it
is ok to think of them as specifying data objects.)
-/

-- false and the empty set
-- typically denoted by ∅ 
def my_empty_set (T : Type) := { t : T | false }

#check (∅ : set nat)    -- 
#reduce (∅ : set nat)   -- the membership predicate
/-
It takes any object (a nat in this case) and returns
the proposition false in all cases. No natural number
satisfies false, so this predicate, λ n, false specifies
the empty set of natural numbers.
-/

example : ∀ (n : nat), n ∉ (∅ : set nat) :=
begin
assume a,
assume h,   -- a ∈ ∅ means ((λ n, false) a), i.e., false
cases h,    -- QED
end 

def my_universal_set (T : Type) := { t : T | true}

example : 7 ∈ my_universal_set nat :=
begin
trivial,
end


-- and (∧) and set intersection (∩)
-- a ∈ S ∩ T means a ∈ S ∧ a ∈ T
def my_set_intersection
  {α : Type} 
  (S T : set α) 
  (a : α):
(a ∈ S ∧ a ∈ T) ↔ (a ∈ S ∩ T) :=  -- learn how to read
begin
split,    -- Lean tactic: applies iff.intro _ _
assume h,
exact h,
assume h,
exact h,
end 

-- or (∨) and set union (∪)
-- a ∈ S ∪ T means a ∈ S ∨ a ∈ T
def my_set_union
  { α : Type } 
  (S T : set α) 
  (a : α) :
a ∈ S ∨ a ∈ T ↔ a ∈ S ∪ T :=   -- learn how to read
begin
split,    
assume h,
exact h,
assume h,
exact h,
end

-- not (¬) and set complement (ᶜ)
-- ¬(a ∈ S) ↔ a ∉ S ↔ a ∈ Sᶜ
def my_set_complement
  { α : Type } 
  (S : set α) 
  (a : α) :
  a ∉ S ↔ a ∈ Sᶜ 
  :=
begin
split,
assume h,
exact h,
assume h,
exact h,
end


-- implication (→) and subseteq (⊆)
-- (S ⊆ T) ↔ (a ∈ S → a ∈ T)
def my_subset_of
  {α : Type} 
  {S T : set α} :
  (∀ a, a ∈ S → a ∈ T) ↔ (S ⊆ T)  -- parentheses on left are essential here
  :=
begin
split,
assume st, 
exact st,    -- don't use same name a for different value
assume h,
assume a,     -- remember S ⊆ T means ∀ a, ..., so assume a
assume as,
exact (h as),
end

/-
set difference, S \ T (all the elements in S that are not in T)
𝐴∖𝐵 = { 𝑥 ∣ 𝑥∈𝐴 ∧ 𝑥∉𝐵}.
-/

def my_set_difference
  {α : Type} 
  {S T : set α} 
  (a : α ):
  (a ∈ S ∧ a ∉ T) ↔ a ∈ S \ T :=
begin
split,
assume h,
exact h,
assume h,
exact h, 
end

/-
Set equality: Next time.
-/

/-
Or maybe relations. Probably relations. Then 
equality. Then set equality in particular.
-/

section foobar

#check 

variables 
  (α β : Type)
  (m: α → β → Prop) 
  (a : α)
  (b : β) 


end foobar