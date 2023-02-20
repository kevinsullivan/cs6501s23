
-- The type of 1 is nat 
#check 1

-- Type type of nat is *Type*
#check nat 

-- The type of all basic computational types is *Type*
#check bool
#check string
#check list bool

-- A natural question: What's the type of Type, etc?
#check Type 
#check Type 0   -- Type is shorthand for Type 0
#check Type 1   -- It's type universes all the way up
#check Type 2   -- etc.

/-
What we have so far then is a hierarchy of "computational"
types like this:

       ...        higher type universes
        |
      Type 1 (the type of objects that contains Type 0 objects)
        |
      Type 0         a type universe
        |        
       nat                type
        |
        1                value

Type Universes
--------------
-/

-- What universes do various objects inhabit
#check nat             -- Type 0 
#check list nat        -- list of nats : Type 0

def list_of_types : list Type := [nat, bool, string]
#check list (Type 0)   -- list of Type 0s : Type 1  
#check list (Type 1)   -- list of Type 1s : Type 2


#check 1 = 1  -- 1 = 1 is a proposition, thus of type Prop
#check ∃ (a b c : ℕ), a*a + b*b = c*c -- also of type Prop

/-
Logical Types
-------------

So just as *Type* (*Type 0*) is the type of all basic data
types, *Prop* is the type of all propositions. And just as
data types can have values (e.g., nat has the value 1), so 
propositional types can have values: these values, if they
exist, serve as *proofs* of the given propositions. You can
even think of *1* as a "proof" of *nat* if that helps you
to see the analogy clearly.

As an example, consider the proposition, *1 = 1*. In Lean
this proposition is a type, and it does have a proof value, 
namely (eq.refl 1). So is the type of (eq.refl 1)? Of course
it's *1 = 1*. Let's see it in Lean.

-- Example: Here's a proof of 1 = 1
def proof_of_1_eq_1 := eq.refl 1

-- What is its type?
#check proof_of_1_eq_1


#check 1 = 1
#check Prop



-- type is 1 = 1
#check proof_of_1_eq_1

-- type is Prop
#check 1 = 1


#check Prop

/-
We can draw a picture now to see how things work.

Prop (Sort 0) --> Type (Sort 1, Type 0) --> Type 1 (Sort 2) --> etc
    |                         |                     |
    |                         |                     |
  1 = 1                      nat                 list Type
    |                         |                     |
    |                         |                     |
eq.refl 1                     1              [nat, bool, string]
-/


-- declare two possible different type Universe levels
universes u v

-- 
#check @prod.mk

-- Here's a function that takes two types in arbitrary universes
def mk_pair (α : Sort u) (β : Sort v) := (α, β)

-- Here are examples of type pairs we can form.
#check mk_pair nat bool 
#check mk_pair (1=1) (2=1)
#check mk_pair (1=1) (list Type)

/-
As another example, here's a thoroughly polymorphic version of
the identity function. Given a type as an argument, it takes a
second value, a, *of that previously given type*, and returns it.
-/

def my_id (α : Sort u) (a : α) := a

-- applications to objects of various types 
#reduce my_id Prop (1=1)
#reduce my_id nat 1
#reduce my_id (list Type) [nat,nat,bool]



-- With {} we tell Lean that α should be inferred automatically
def my_id' { α : Sort u } (a : α) := a

-- Now we don't provide the type arguments explicitly
#reduce my_id' (1=1)
#reduce my_id' 1
#reduce my_id' [nat,nat,bool]

-- If necessary through, we can turn off implicit inference using @
#reduce @my_id' Prop (1=1)
#reduce @my_id' nat 1
#reduce @my_id' (list Type) [nat,nat,bool]

