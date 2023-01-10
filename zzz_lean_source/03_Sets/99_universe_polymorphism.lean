/- Universe polymorphism

Type universes as you know them so far:

  Sort 0    Sort 1    Sort 2    Sort 3 ...
  Prop      Type      Type 1    Type 2 ...

Type is short for Type 0 and for Sort 1. 

Prop is special. Types in Prop specify
propositions. All values of such a type 
are considered equal and equally good as
proofs. 


Sometimes we want to be able to specify that 
any sort (whether Prop, Type, or some higher
type Universe) will do as the value of some 
type parameter. The utility is that we extend
the notion of polymorphism across all universe 
levels: 0, 1, 2, ... (all natural numbers).

In cases where we want definitions with this 
higher level of generality, we can declare a
"universe variable" and use it as an explicit
universe level parameter to Sort or Type.
-/

universe u      -- universe variable
#check Sort 0
#check Sort 1
#check Sort u   -- used here
#check Type 0
#check Type

/-
As an example, here's a super-general definition
of the identity function. For any type universe u
(from above) and any (implicit) "type" α, funk will
take and then just return any value a of type α. We
give a few example expressions
-/
def funk {α : Sort u} (a : α) : α := a
#reduce funk 1            -- a is 1, so α = ℕ, so u = 1
#reduce funk (1 = 1)
#reduce funk nat          --
#reduce funk Prop         --
#reduce funk Type         --
#reduce funk (Type 0)     --
#reduce funk (Sort 1)     --
#reduce funk (Sort 2)     -- etc.



/-
Continuing with our example, it should now be clear that
the "funk" function is really just the identity function
on objects of any types in any type universe, from Prop
through Type on up. 
-/

example : funk (1 = 1)  = (1 = 1) := rfl  --
example : funk nat      = nat     := rfl  --
example : funk (Sort 0) = Prop    := rfl  --
example : funk (Type 0) = Type    := rfl  --
example : funk (Sort 1) = Type    := rfl  --
example : funk (Sort 2) = Type 1  := rfl  -- etc.
example : funk (Sort 2) = Type 2  := rfl  -- nope

/-
Takeaway I: If you want maximally general parametric
polymorphism, generalize over universe levels, as in
the preceding example. When you see an argument of type, 
Sort u, you're looking at parametric polymorphism, with
type arguments from any universe level. 
-/



/- Optional

Higher-universe types, by the way, have values 
that themselves contain types as "field values." 
The type of a type-containing object will inhabit
the universe one higher than that of the highest
universe levels of any of its contained types.
-/


