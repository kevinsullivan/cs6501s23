inductive bit : Type
| zero
| one

/-
You've already seen inductive definitions in Type: in
our Bit example, which we repeat here.
This definition establishes bit as a data type with
two parameterless (constant) constructors: zero and
one. A core property of inductively defined types is
that their values are exactly those provided for by
constructors. So zero and one are all of the values
of our bit type. Key idea: bit is now a type, like
nat or bool, with values bit.zero and bit.one. 
-/

#check bit.zero
#check bit.one

/-
We cross a bridge that really conntects computing and 
logicc. We unpack a key definition of equality in Lean. 
A few examples will help explain its operation.
-/

/-
Π {β : Type}, (β → β → Prop) → Prop

Again, think of Π as ∀. We define reflexive, given 
a type β, to be a predicate on binary relations on 
β. Some relations are reflexive,some aren't: some
have the property of being reflexive (reflexivity),
some don't. The reflexive predicate "picks out" the
relations that have this property: it's the ones
for which there is a proof. And once we've defined
reflexive as a predicate on relations, we can even
talk about the *set of all reflexive relations on 
values of a given type, β.* Here is how we write 
this set using reflexive as a predicate in a set
builder expression.
-/

def reflexive_relations := 
  { r : β → β → Prop | reflexive r }

-- That's cool. It says a lot very concisely.

/-
Now we can even state and prove theorems about
relations being reflexive using the language
of *set theory* by asserting that a relation 
is *in this set* 
-/
example : @eq nat ∈ @reflexive_relations nat := 
begin
  -- next three lines optional, for pedagogical clarity
  show reflexive_relations eq,
  unfold reflexive_relations,
  show reflexive (@eq nat),
  exact eq_is_refl,      -- Already proved, use theorem!
end



