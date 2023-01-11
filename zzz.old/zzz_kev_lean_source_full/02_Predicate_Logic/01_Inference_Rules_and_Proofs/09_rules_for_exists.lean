/- INFERENCE RULES FOR ∃ PROPOSITIONS

There are two inference rules for ∃ propositions: 
one introduction, one elimination. In Lean they are
called exists.intro and exists.elim. We will usually
use the cases tactic to apply the elimintion rule and
clean up the results. We generally apply the intro
rule directly. 
-/

/- Introduction Rule for ∃ 

Let's start with introduction. We give several proofs
of the proposition that "there exists n even number."
To construct such proof, one applies the introduction
rule to two arguments: a particular number, n, and a
proof that *that* number is even. As you can see in the
next three examples, it doesn't matter what number you
give as a first argument, as long as you can give a proof
that it's even as it's second argument. This works for
the first argument values of 6 and 8 (because there are
easy proofs that they're even) but not for 7 (because
it's not even).
-/

def isEven (n) := n%2 = 0

example : ∃ (n : ℕ), isEven n := 
  exists.intro 6 rfl           -- 6 is good witness

example : ∃ (n : ℕ), isEven n := 
  exists.intro 7 rfl           -- no proof 7 is even

example : ∃ (n : ℕ), isEven n := 
  exists.intro 8 rfl           -- 8 is good, etc.

/-
In summary, to prove ∃ (x : T), P x, apply exists.intro
to a particular value, (t : T), and to a proof of (P t),
that that particular value, t, has the property (e.g.,
of being even) specified by the predicate, P.
-/

/- Elimination rule for ∃

Now for the elimination rule. What can we deduce or derive
from a given proof of ∃ (x : T), P x? Simply put, we can
deduce that, for some particular but otherwise unspecified
value, w : T, there is also a proof of P w, that w has the
property in question.
-/

/-
Here's a trivial example, where we will assume we have a proof
of an existentially quantified proposition, just to see what we
can do with it.
-/
example : (∃ (n : ℕ), isEven n) → true :=
begin
assume h,
cases h with w pf,
-- that illustrates the point we wanted to make
-- look at the context: you deduced that there is
-- a "w" for which there's also a proof of isEven w.
end

/-
Here's a more interesting example. We prove that
"if there's a ball that's both blue and round then
there is a ball that's blue." 
  
How would you prove this in English? Well, from 
the assumption that there's a ball that has both
properties, we can deduce there's some specific
ball, w, for which there is a also proof of the
proposition, isBlue w ∧ isRound w, *about that
specific ball*. 

We can "eliminate" the ∧ to obtain separate 
proofs of isBlue w and isRound w. Then we can
finish the proof by applying exist.intro to that
same ball, w, and to a proof that it's blue. That
proves that there exists a blue ball, which is 
what we wanted to prove. QED. 
-/

-- Here's exact that argument formally
example 
  (Ball : Type)                             -- There is a type of object, Ball
  (isBlue : Ball → Prop)                    -- a predicate on objects of this type
  (isRound : Ball → Prop) :                 -- a second predicate on objects of this type
  (∃ (b : Ball), isBlue b ∧ isRound b) →    -- if there's a ball that satisfies both
  (∃ (b : Ball), isBlue b) :=               -- then there's a ball that satisfies one
begin
  assume h,                                 -- assume there's a ball that's blue and round
  cases h with b br,                        -- derive a specific ball, w, and a proof, br 
  cases br with blue round,                 -- split the proof of the conjunction into parts
  exact exists.intro b blue,                -- construct a proof that there's a blue ball
end

/-
Here are (our local versions of) the intro and elim 
inference rules for ∃. Before each one we use #check
to display Lean's "native" version.
-/

-- ∃ introduction

#check @exists.intro      -- Think of "Sort u" as just Type 

def exists_intro := 
  ∀ {X : Type}            -- for any type, X 
    {P : X → Prop}        -- for any predicate on values of this type
    (w : X),                -- if you give a witness w
    P w →                   -- then if you give a proof that w satisfies P
    (∃ (x : X), P x)        -- you get a proof there exists an x that satisfes P


-- ∃ elimination

#check @exists.elim

def exists_elim := 
  ∀ {X : Type}              -- for any type, X 
    {P : X → Prop}          -- for any predicate on values of this type
    {Y : Prop},             -- for any "concluding" proposition, Y
    (∃ (x : X), P x) →      -- if we're given a proof that there's an x satisfying P
    (∀ (x : X), P x → Y) →  -- then if for every x that satisfies P Y is true
    Y                       -- then Y is true

#check @exists.elim
/- Compare Lean's definition with ours
  ∀ {α : Sort u_1} 
    {p : α → Prop} 
    {b : Prop}, 
    (∃ (x : α), p x) → 
    (∀ (a : α), p a → b) → 
    b
-/

/-
We can of course prove that our version of the rule
is valid, because it is. Here it goes.
-/
example : exists_elim :=
begin
unfold exists_elim,
assume X,   -- some type
assume P,   -- some property of values of that type
assume Y,   -- a goal to be proved from an "exists" proof
assume exists_x_with_P,           -- an exists proof
assume if_any_x_has_P_then_Y,     -- that any x with P implies Y
cases exists_x_with_P with w Pw,  -- eliminate ∃ to get witness and proof
exact (if_any_x_has_P_then_Y w Pw), -- use them to finish proof
end 

/-
Question: Would the preceding proposition be true 
if you just dropped the condition, (∃ (x : X), P x)? 
The answer is no, but why? There's an edge case that
the existence proof eliminates. What's the edge case? 
Answer: That there are no x's with property P. (You
should be sure to understand this point!)
-/

/- 
Example: Let's formalize and prove the proposition
that if there's someone everyone loves, then everyone 
loves someone.
-/
example 
  (Person : Type)                     -- people
  (Loves : Person → Person → Prop)    -- loves relation
  :
  -- formalized version of the informal proposition
  (∃ (p : Person), ∀ (q : Person), Loves q p) →
  (∀ (p : Person), ∃ (q : Person), Loves p q)
  :=
begin 
  assume h,
  cases h with lenny everyone_loves_lenny,
  assume bruce,
  apply exists.intro lenny _,
  apply everyone_loves_lenny bruce,
end 

/-
Proof: Assume there's someone everyone 
loves. By exists elimination let's call that
person lenny and deduce that everone loves
lenny. Now pick an arbitrary person, let's 
call him or her bruce. We have to show that
there's someone bruce loves. But everyone
loves lenny, so bruce loves lenny (∀ elim). 
QED.
-/