/-*** #check ***-/

/-
In Lean, the #check command is part of Lean but not part of
predicate logic. It takes any expression does two things:

(1) It checks it for syntax errors
(2) If it's syntactically correct, it tells you its type

Let's look at some examples. Hover over the blue squiggle.
-/

#check 5    -- 5 is a good expression; it's type is ℕ (natural number)
#check ℕ    -- ℕ is a data type so *it's& type is Type


/-
The type of the value 5 is ℕ
The type of ℕ is Type
Type is the type of every simple data type in Lean
-/


/-
Let's look at another example
-/

#check "Hi"   -- "Hi" is a value true of the string data type
#check string -- string is a data type so it's type is also Type


/-
The type of 5 is ℕ (5 : ℕ) and the type of ℕ is type (ℕ : Type)
The type of "Hi" is string ("Hi" : string") and the type of string is type (type : Type)
Similarly in Lean, the type of tt is bool (tt : bool) and the type of bool is Type (bool : Type)
In Lean, the type of every basic data type is just Type. Types are values, too, in Lean.
That let's us express ideas such as this: every value, t, of every data type T, equals itself
-/

#check ∀ (T : Type) (t : T), t = t
-- for every type T, and every value t of this type, t = t.


/-
Now let's look at using #check to check expressions involving propositions. 
-/

#check ∀ (P : Prop), P ∨ ¬P

/-
The expression, ∀ (P : Prop), P ∨ ¬P, is syntactically correct;
and because this value is a proposition, it's type is Prop. The 
type of any proposition our higher-order predicate logic is Prop. 
Here's another example.
-/

#check 0 = 1

/-
The expression 0 = 1 is a syntactically correct proposition,
and because it's a proposition, it's type is also Prop
-/

#check true

/-
The logical expression, true, is also a proposition,
so it's type is also Prop.
-/

#check true.intro 

/-
Finally we again see that propositions, themselves
of type, Prop, are also types; just like string or
bool are of type, Type, but are themselves types as
well. 
-/

#check bool
#check tt

#check true
#check true.intro

/-
Proofs (or "proof objects" or "proof terms") in 
Lean are values of logical/propositional types.
It's strange, but every proposition is its own
type in the higher-order constructive logic of
Lean. That is to say, in type theory, which you
now understand pretty well!
-/

/-
Extra! So what's the type of Prop, or of Type?
In the following diagrams, --> means "has type."
So, for example, Prop has type Type 0, which in
Lean we can and usually do write just as "Type."

Prop   --> Type 0 --> Type 1 --> Type 2, ad inf.
Sort 0 --> Sort 1 --> Sort 2 --> Sort 3, ad inf.
-/

-- You can see it for yourself using #check

-- Here with computational types
#check 0
#check nat
#check Type
#check Type 0
#check Type 1
-- ad infinitum

-- Here with logical types
#check true.intro -- a proof is a value
#check true       -- a proposition is a type "in" Prop  
#check Prop       -- the type of Prop is Type 
#check Type 1     -- etc.
-- ad infinitum

/-
Prop gets special treatment. In particular, and two
proofs of any propositional type are considered to be
equal, because they are considered to be equally good
*as proofs*. This is certainly not the case for values
of types that "live in" Type. Take bool, for example.
It has two obviously unqual values, tt and ff in Lean.
But suppose we have an arbitrary proposition, P, and
two arbitrary proofs of it. Lean will treat them as
being equal. 
-/

example (P : Prop) (pf1 pf2 : P) : pf1 = pf2 := rfl

/-
Cool! Note by the way that here we used Python/C-style
"code" by declaring named arguments before the colon.
We could have avoided that by binding names to formal
parameters after the colon, with the same effect.
-/

example : ∀ (P : Prop) (pf1 pf2 : P), pf1 = pf2 := 
begin
assume P p1 p2,
exact rfl,
end 
