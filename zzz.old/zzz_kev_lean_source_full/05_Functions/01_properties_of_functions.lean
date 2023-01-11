namespace cs2120

section functions

variables
  {α β : Type}        -- any two data types
  (r : α → β → Prop)  -- any binary relation
/-
I've simplified α and β to be ordinary types
compared to what I presented in lecture. This
just makes things a little simpler here.
-/

-- Single-valued in "relational algebra" means not one-to-many
def single_valued := ∀ (a : α) (b c : β), r a b → r a c → b = c 

-- A function is a single-valued relation; these are synonyms
def function := @single_valued α β  

/-
Note: Compared to lecture, I've related single_value with
function in the following definitions. The meanigns are of
course equivalent, but the meaning is expressed more clearly
here, as the term, injective (and surjective and bijective,
below) apply only to relations that are also functions. 
-/

-- A function is injective if it's not many-to-one
def injective := ∀ (a b : α) (c : β), 
  function r → r a c → r b c → a = b

/- 
A function is total if it is defined for every element 
of the domain: that is, if every "input/α" value has
a corresponding "output/β" value.
-/
def total_function := 
  function r → ∀ (a : α), ∃ (b : β), r a b 


/-
A strictly partial function is one for which there is
some input/α value with no corresponding output/β value. 
Mathematicians sometimes consider total functions also
to be partial functions, so we use the term "strictly
partial" to refer to functions that are not total.
-/
def strictly_partial := function r → ∃ a, ¬ ∃ b, r a b
-- In lecture I omitted the condition that r is a function 

/-
A function is said to be surjective if it "covers" the
co-domain, which is to say the set in which the output
values "live." In other words, for every element of the
output/β set/type, there is some element in the input/α 
set/type that is related to that output value.
-/
def surjective := function r → ∀ b, ∃ a, r a b

/-
A function is said to be bijective if it is injective
(one to one, not many-to-one) and and surjective (the
output/co-domain set/type is covered).
-/
def bijective := injective r ∧ surjective r


/-
In Lean, "functions" that compute are necessarily total.
For *any* value of their input type, they have to return
some value of the output type. You can see this clearly 
in the definition of the function type notation, α → β,
as ∀ (a : α), β -- that for *every* value of type α such
a function must return some value of type β. 

So how do we represent a strictly partial function in 
Lean or in a similar proof assistant? Rather than using
a computation definition, we use a logical definition!

Here we will define a partial relation between values 
of two types, Person and ℕ. Think of it as returning
the driver's license id number of a given person. No
person has several id_numbers (or they shouldn't in 
any case!) so the relation is a function. However not
eery person has an id_number, so we have a strictly
partial function.

To keep things simple, we'll model a toy world in 
which there are only three people. Let's just call
them p1, p2, and p3. We'll thus define Person as a
data type with just three values. 
-/

inductive Person : Type
| p1 : Person
| p2 : Person
| p3 : Person

-- To avoid having to type Person.p1, etc. we ...
open Person   -- ... open the person namespace.


/-
Now comes the new part! We define the id_number
relation as a kind of parameterized data type.
That's what "inductive" means in the following
definition. id_number takes a person and an id
number as parameters and yields a *proposition*,
that we understand as asserting that that person
has that id number. The trick is that we go on
to define the proofs that are available to prove
such propositions. In this case, we define pf1
to be a proof of id_number p1 1 (that the person
p1 has id number 1), and pf2 to be a proof that
person p2 has id_number 2. *We do not define a
proof that p3 has a corresponding id number, so
it doesn't!* We thus specify the strictly partial 
function, id_number = { (p1, 1), (p2, 2) }. 
-/
inductive id_number : Person → ℕ → Prop 
| pf1 : id_number p1 1
| pf2 : id_number p2 2

open id_number  -- open the namespace


/-
Now with all this machinery set up, we are in a
place where we can state and prove propositions
such as this: id_number is an injective function. 
You can easily see that it's injective, in that
no two distinct "people" with the same id. Now
we'll prove it.
-/

example : injective id_number := 
begin
-- By the definition of injective ...
unfold injective,

-- we are to ...
show ∀ (p1 p2 : Person) (idn : ℕ), 
  function id_number → 
  id_number p1 idn → 
  id_number p2 idn → 
  p1 = p2,

-- Let person1 and person2 be arbitrary persons 
intros person1 person2,

-- Assume id is an arbitrary id number (nat), ...
intro id,

-- that id_number is a function, ...
assume id_number_is_func,

-- and that p1 and p2 each have id number "id"
assume person1_id person2_id,

-- To show id_number is injective we must ...
show person1 = person2,

/-
From here the proof is by case analysis on 
person1 and person2, each of which can have
one of three values (p1, p2, p3), giving us
nine cases to consider. All the cases where
person1 ≠ person2 yield contradictions and 
so can be ignored as impossibilities, while
there are proofs in the three cases where
person1 = person2. That'll do it. Here it
goes
-/
-- case analysis person1 (p1, p2, p3)
cases person1,

-- case person1 = p1

    -- case analysis person2 (p1, p2, p3)
    cases person2,

    -- case #1: person1 = p1, person2 = p1
    exact rfl,    -- they're the same person

    -- case #2: person1 = p1, person2 = p2

    /-
    Remember that case analysis gives you
    one case for each way a given value/proof
    can be constructed, including arguments 
    to the presumed constructors. Here case
    analysis on person1_id reveals that the only
    way to construct this proof is if id_num
    is 1. 
    -/
    cases person1_id,
    /- 
    But now there is no way to construct 
    person2_id. With no cases to consider due
    to contradiction, we can just ignore 
    this case, a form of false elimination.
    -/ 
    cases person2_id,


    -- case #3: person1 = p1, person2 = p3
    -- Proof is same style as case #2
    cases person1_id,
    -- but now person2_id cannot be 
    cases person2_id,



-- case person1 = p2

    -- case analysis person2 (p1, p2, p3)
    cases person2,

    -- case #4: person1 = p2, person2 = p1
    cases person1_id,
    cases person2_id,

    -- case #5: person1 = p2, person2 = p2
    exact rfl,

    -- case #6: person1 = p2, person2 = p3
    -- p3 has no id, so no cases to consider
    cases person2_id,

-- case: person1 = p3

  -- case analysis person2 (p1, p2, p3)
  cases person2,

  -- case #7: p3 has no id
  cases person1_id,
  -- case #8: p3 has no id
  cases person1_id,
  -- case #9: p3 has no id
  cases person1_id,

/- 
The only way that the conditions can be
satisfied is if person1 = person2, which
shows that the function is injective: no
two distinct people have the same id in
the *partial function* specified by the 
definition of id_number.

QED.
-/

end

end functions

-- Lean has its own definitions of these properties

end cs2120



