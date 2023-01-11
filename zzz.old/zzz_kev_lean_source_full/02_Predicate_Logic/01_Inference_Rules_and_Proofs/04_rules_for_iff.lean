section pred_logic

variables X Y Z : Prop

/- *** IFF *** -/

-- ↔ 
def iff_intro         := (X → Y) → (Y → X) → X ↔ Y

/-
You can read this rule both forward (left to right) and 
backwards. Reading forwards, it says that if you have a
proof (or know the truth) of X → Y, and you have a proof
(or know the truth) of Y → X, then you can derive of a proof
(deduce the truth) of X ↔ Y.

The more important direction in practice is to read it
from right to left. What it says in this reading is that
if you want to prove X ↔ Y, then it will suffice to have
two "smaller" proofs: one of X → Y and one of Y → X. 

From now on, whenever you're asked to prove equivalence
of two propositions, X and Y, you'll thus start by saying,
"It will suffice to prove the implication in each direction."
Then you end up with two smaller goals to prove, one in 
each direction. So, "We first consider X → Y." Then give
a proof of it. Then, "Next we consider Y → X." Then give
a proof of it. And finally, "Having proven the implication
in each direction (by application of the rule of ↔ intro)
we've completed our proof. QED."
-/

def iff_elim_left     := X ↔ Y → (X → Y)
def iff_elim_right    := X ↔ Y → (Y → X)

/-
The elimination rules are also easy. Given X ↔ Y, you can
immediately deduce X → Y and Y → X.
-/

end pred_logic

