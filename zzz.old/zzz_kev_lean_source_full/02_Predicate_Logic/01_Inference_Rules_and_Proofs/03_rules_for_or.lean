/- A LEAN DETAIL and IMPORTANT LANGUAGE DESIGN CONCEPT
A good language gives you good ways not to repeat yourself.
We can avoid having to repeatedly write "∀ (X Y : Prop),"
by creating a "section" in a Lean file, and declaring the
common variables once at the top. Lean then implicitly adds
a "∀ (X : Prop)" at the beginning of any expression that has
an X in it (and the same goes for Y and Z in this file).
I
-/

section pred_logic

variables X Y Z : Prop

/-
In your mind, be sure to recognize that every one of the
following propositions now has an implicit ∀ in front. The
or_intro_left definition that comes next, for example, means 
def or_intro_left : Prop := ∀ (X Y : Prop), X → X ∨ Y. 
-/


/- *** OR *** -/

-- ∨ 
def or_intro_left : Prop    := X → X ∨ Y
def or_intro_right : Prop   := Y → X ∨ Y
def or_elim : Prop          := (X ∨ Y) → (X → Z) → (Y → Z) → Z

/-
Lean, and other languages like it, also allow you to drop
explicit type judgments when they can be inferred from the
context. In the rest of this file, we also drop the ": Prop"
explicit type judgments because Lean can figure our from the
values that follow the :='s that type types of the variables
here just have to be Prop.
-/

/-
Quiz questions. 

Suppose you know that (X → Z) and (Y → Z) are true and you 
want to prove Z. To be able to prove Z it will *suffice* to 
prove ______; for then you will need only to apply the ______
rule to deduce that Z is true.

Suppose you know that (X → Z), (Y → Z), and Z are all true.
Is it necessarily that case that (X ∨ Y) is also true? Defend
you answer.

Suppose it's raining OR the sprinkler is running, and that in
either case the grass is wet. Is the grass wet? How would you
prove it?
-/

end pred_logic