/- TEXT:
*********************
Propositions as Types
*********************

In the last section, we build on all of the ideas of
the last chapter to gain an understanding of higher
order predicate logic in Lean. Each section of this
chapter focuses on a dimension in which the latter is
different, often a powerful generalization, of ideas
from the last chapter.

As an example, in the last chapter, we represented
propositions as terms of our data type, *prop_expr*. 
We  also saw that we could formulate inference rules of 
propositional logic to provide a way to reason about
the truth of given propositions. In this chapter, we
will represent propositions as types of a special kind,
instead, and proofs as values of these types. We will
then adopt exactly the same inference rules we saw in
the last chapter, but generalized to this far more
expressive logic.   

To warm up for the idea that propositions are (represented as)
types (in type theory), as an example we'll first look at the 
types related to the natural number, 1. Then we'll analyze the
types of a few propositions, namely 1 = 1 and 0 = 1. The take
away message will be that propositions are special types that
live in their own *type universe* and values of such types (if
there are any) serve as *proofs* of such propositions. 

Computational Types
-------------------
TEXT. -/

-- QUOTE:
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
-- QUOTE.

/- TEXT: 

Logical Types (Propositions)
----------------------------

Now we'll turn to the idea that propositions are types of 
a logical kind. In Lean and related proof assistants and in
type theory more generally, propositions are represented as 
*types* that inhabit a special type universe: in Lean, Prop.
TEXT. -/

-- QUOTE:
#check 1 = 1  -- 1 = 1 is a proposition, thus of type Prop
#check ∃ (a b c : ℕ), a*a + b*b = c*c -- also of type Prop
-- QUOTE.

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
TEXT. -/

-- QUOTE: 
-- Example: Here's a proof of 1 = 1
def proof_of_1_eq_1 := eq.refl 1

-- What is its type?
#check proof_of_1_eq_1
-- QUOTE.

/- TEXT:
In Lean, types are terms, too, and so they have types, as we
have already seen. So what is the type of *1 = 1*. It's Prop.
As we've said, logical types (propositions) inhabit the type
universe, Prop, also known as Sort 0.
TEXT. -/

-- QUOTE:
#check 1 = 1
#check Prop
-- QUOTE.


/- TEXT:
Now we can clearly see the type hierarchy. Each proposition 
is a type, and all such types are in turn of type, Prop. We we
have the following picture of the type hierarchy for the
terms we've just constructed.
TEXT. -/

-- QUOTE:
-- type is 1 = 1
#check proof_of_1_eq_1

-- type is Prop
#check 1 = 1
-- QUOTE.

/- TEXT:
You might finally ask, what is the type of Prop? It's Type!
TEXT. -/

-- QUOTE:
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
-- QUOTE.

/- TEXT: 

Type Universe Levels
--------------------

In the top row we have a hierarchy of type universes, starting 
with Sort 0 and extending up. Prop is the common name in Lean for
Sort 0, and Type is the common name for Sort 1. In the second row
are examples of types that inhabit each of the universes. *1 = 1*
for example is a logical type (a proposition) in Prop, while nat
is a computational type in Type. Finally, *list Type* is the type 
of lists of terms each of type Type, i.e., lists of computational
types. The bottom row gives examples of values of each of the types
above: *eq.refl 1* is a proof/value of (type) *1 = 1*; 1 is a value
of type *nat*; and *[nat, bool, string]*, because it contains as
elements values of type Type 0 is itself a value of type Type 1. 

As a final comment, Lean allows one to generalize over these
type universes. To do so you declare one or more *universe 
variable* which you can then use in declaring types. Lean can
also infer universe levels.
TEXT. -/

-- QUOTE:
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
-- QUOTE.


/- TEXT:
Implicit Arguments
------------------
TEXT. -/

-- QUOTE:
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
-- QUOTE.

