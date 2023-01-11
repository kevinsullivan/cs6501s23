/- AND
-- X, Y ⊢ X ∧ Y              -- and introduction
-- X ∧ Y ⊢ X                 -- and elimination left
-- X ∧ Y ⊢ Y                 -- and elimination right
-/
#check @and.intro       -- ∀ {a b : Prop}, a → b → a ∧ b
#check @and.elim_left   -- ∀ {a b : Prop}, a ∧ b → a
#check @and.elim_right  -- ∀ {a b : Prop}, a ∧ b → b



/- OR
-- X ⊢ X ∨ Y                -- or introduction left
-- Y ⊢ X ∨ Y                -- or introduction right
-- X ∨ Y, X → Z, Y → Z ⊢ Z  -- or elimination
-/
#check @or.inl          -- ∀ {a b : Prop}, a → a ∨ b
#check @or.inr          -- ∀ {a b : Prop}, b → a ∨ b
#check @or.intro_left   -- ∀ {a : Prop} (b : Prop), a → a ∨ b
#check @or.intro_right  -- ∀ (a : Prop) {b : Prop}, b → a ∨ b
#check @or.elim         -- ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c

/-
Use inl or inr when Lean can infer the other disjunct,
otherwise use intro_left or intro_right, where you have
to give the other disjunct (a proposition, not a proof)
as an explicit argument.
-/

/- FORALL, ARROW
Arrow is a special case of ∀ in Lean, and ∀ is built
into the very core of the logic. There are no rules
called forall.intro or forall.elim. Rather, you prove
a forall or arrow proposition by *defining a function*
that takes a value/proof of the premise/argument and
that returns a value/proof of the conclusion. On the
other hand, forall/arrow elimination is by *applying*
such a "function/proof" to an argument of the right 
kind to obtain a result of the right kind.

Insight: Whenever you define a function (in Python,
for example), you declare formal parameters (arguments)
and then, within the body of the function, you *assume*
that you've been given actual parameter values of the
right types, and then you write a that constructs and
returns a result of the right type . That is exactly
what you're doing when you use forall/arrow introduction: 
assume you've been given actual arguments of the right
types then  show that you can construct and return a 
value of the specified "return" type. This works in
Lean whether the types and values you're working with
are computational (numbers, strings, etc) or logical
(propositions, proofs). 
-/

/-
There are several formats for writing functions in 
Lean. Let's start with a computational example: a
simple function that takes a string, str, and returns
its length. The following four definitions are all
equivalent!
-/

-- use → introduction
def slength1 : string → nat :=
begin
assume (str : string),  -- assume given s of type string
exact (str.length)      -- defined in Lean's libraries
end

def slength2 : string → nat 
| str := str.length     -- matches str to first argument

-- ∀ introduction
def slength3 : ∀ (s : string), nat :=
begin
intro str,              -- assume given (str : string)
exact (str.length)      -- defined in Lean's libraries
end

-- almost ordinary function definition
-- argument declared/named *before* the color
def slength4 (str : string) : nat := 
begin
  exact str.length
end

-- Python/C++ style
def slength5 (str : string) : nat := str.length

-- ∀/→ introduction is function definition
-- ∀/→ elimination is function application 

#eval slength1 "Lean is actually very cool!"
#eval slength2 "Lean is actually very cool!"
#eval slength3 "Lean is actually very cool!"
#eval slength4 "Lean is actually very cool!"
#eval slength5 "Lean is actually very cool!"

/-
And of course it works for logical types and
proofs just as well as for data/computational
types and ordinary data values. Here are three
ways to prove that any proposition P implies
true, for example.
-/

-- Using → 
lemma foo0 : Prop → true :=
begin
  assume (P : Prop),  -- bind name to assume argument
  exact true.intro    -- return result of right type (true)
end

lemma foo1 : Prop → true
| P := true.intro

-- Using ∀ 
lemma foo2 : ∀ (P : Prop), true :=
begin 
intro P,          
exact true.intro, 
end

-- Python/C style but using script to generate proof "term"
lemma foo3 (P : Prop) : true :=
begin
exact true.intro
end

-- Python/C style returning exact proof term
lemma foo4 (P : Prop) : true := true.intro

-- Each function is a proof of Prop → true
#check foo0
#check foo1
#check foo2
#check foo3



/- NOT
-- ¬X means (X → false)   -- negation introduction
-- ¬¬X ⊢ X                -- negation elimination 
-/
-- introduction: to prove ¬X, use → introduction
-- (double) ¬ elimination is proof by contradiction 
#check @classical.by_contradiction  -- ∀ {p : Prop}, (¬p → false) → p


/- IFF
-- X → Y, Y → X ⊢ X ↔ Y     -- iff introduction
-- X ↔ Y ⊢ X → Y            -- iff elimination left
-- X ↔ Y ⊢ Y → X            -- iff elimination right
-/
#check @iff.intro     -- ∀ {a b : Prop}, (a → b) → (b → a) → (a ↔ b)
#check @iff.mp        -- ∀ {a b : Prop}, (a ↔ b) → a → b
#check @iff.mpr       -- ∀ {a b : Prop}, (a ↔ b) → b → a


/- EXISTS

The one remaining set of inference rules we have
to cover are for ∃. We will cover them after the
mid-term.
-/

/-
Yay! Except for exists, you have now learned *all* of the
inference rules of higher-order predicate logic in Lean, 
which are all also inference rules in classical first-order
logic.  Yay, again! Good work.
-/
