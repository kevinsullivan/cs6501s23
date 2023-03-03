/- TEXT: 
*****************
Polymorphic Lists
*****************

Data Type
---------
TEXT. -/

-- QUOTE:
#check list
-- QUOTE. 

/- TEXT:
The list data type is surprising similar to the nat
data type. Where as a larger nat is constructed from
only a smaller nat, a larger list is constructed from
a new first element (the *head* of the new list) and 
a smaller list (the *tail* of the new list). This type
builder enables us to represent lists of values of any
type and of any finite length.
TEXT. -/

namespace poly_lists

-- QUOTE:
universe u
inductive list (T : Type u)
| nil : list
| cons (hd : T) (tl : list) : list
-- QUOTE.
end poly_lists

-- QUOTE:
-- example: let's represent the list of nats, [1,2,3]
def three_list_nat'' :=
  list.cons   -- takes two arguments
    1         -- head of new list
    (         -- tail list of the new list 
      list.cons   -- etc.
        2
        (
          list.cons
            3
            list.nil
        )
    )

-- it seems to have worked 
#reduce three_list_nat''
-- QUOTE.

/- TEXT: 
Notations
---------
TEXT. -/

-- QUOTE:
-- notation, :: is infix for cons
-- [] notation adds nil at end
def three_list_nat''' := 1::2::3::list.nil
def three_list_nat'''' := [1,2,3]
def four_list_nat := 0::[1,2,3]       -- fun!
-- QUOTE.

/- TEXT:
Operations
----------
TEXT. -/

-- QUOTE:
-- list prepend analogous to nat increment
def prepend' (α : Type) (a : α) (l : list α) :=
  list.cons a l

def three_list_nat' :=
  prepend' nat
    1
    (prepend' nat
      2
      (prepend' nat
        3
        list.nil
      )
    )

#eval three_list_nat'

-- here with an implicit type parameter, making it equivalent to cons
def prepend {α : Type} (a : α) (l : list α) :=
  list.cons a l

def three_list_nat :=
  prepend 
    1
    (prepend
      2
      (prepend
        3
        list.nil
      )
    )

-- okay, that looks good
-- but know that to which it desugars

example := prepend' nat 2 [3,4,5]
#eval prepend' nat 2 [3,4,5]

example := prepend 2 [3,4,5]
#eval prepend 2 [3,4,5]

#eval 2::[3,4,5]
-- QUOTE.


/- TEXT:
Partial Functions
-----------------

Now we face some interesting issues. Our aim is to define
functions that *analyze* lists and return parts of them.
The problem is that there are no parts when a given list
is empty. 

When we defined pred, above, we defined pred of zero to be 
zero (rather than to be undefined). Doing that makes the 
function total and easily represented as a function (lambda 
abstractraction) in Lean. However, in a different application
we really might want to define pred 0 to be undefined, not 0.

A similar set of issues arises when we consider head and
tail functions on lists. When given non-empty lists there
is no problem. But what to do with an empty list argument?
There is no head or tail element to return, yet some value
of the specified type *has to be* returned. 

Let's see some fo the solutions that are available.

Default Value
~~~~~~~~~~~~~
TEXT. -/

-- QUOTE:
-- a version of tail that "loops at zero" 
def tail' : ∀ {α : Type}, list α → list α 
| α list.nil := list.nil 
| α (h::t) := t
#eval tail' [1,2,3,4,5]
-- QUOTE.

/- TEXT:
One nice thing about this solution
is that the function type is still about as natural as
can be: list α → list α.

Option Values
~~~~~~~~~~~~~

The next solution changes the type of the function,
so that return value is in the form of a *variant* 
type, a value of which is either *none* or *some 
valid return value*.
TEXT. -/

-- QUOTE:
def head'' : ∀ {α : Type}, list α → option α 
| α list.nil := none
| α (h::t) := some h

#eval head'' [1,2,3]
#eval @head'' nat []
-- QUOTE.

/- TEXT:

Precondition
~~~~~~~~~~~~

Finally, we can define a version of head' that (1) typechecks
as being a total function, (2) can never actually be applied
fully to an empty list, in which case (3) no real result has 
to be specified to "prove the return type" because such a case 
can't happen. It would be a contradiction if it did, and so it
can be dismissed as an impossibility. Magic: It *is* a total 
function, but it can never be fully appied to an empty list
because a required proof argument, for *that* list, can never
be given; so one can dismiss this case by false elimination,
without having to give an actual proof of the conclusion. 

Consider a head function. It returns the head element from
a non-empty list, but is undefined mathematically when it's
applied to an empty list. The key idea in the next design
is that we can embed a *precondition* for application of
the function, namely that the given list not be empty. Let's
see how e might first write the function using a tactic 
script, to take advantage of your familiarity with using
it to build proofs.  
TEXT. -/

-- QUOTE:
def head' : ∀ {α : Type} (l : list α), (l ≠ list.nil) → α 
|  α l p := 
begin
cases l,
contradiction,
exact l_hd,
end 

-- When applying it a proof about the first argument has to be given 
#eval head' [1,2,3] begin contradiction end   -- proof as a proof script
#eval head' [1,2,3] (by contradiction)        -- alternative syntax, fyi
#eval head' ([] : list nat) _                 -- you'll need a proof of list.nil ≠ list.nil!
-- QUOTE.

/- TEXT:
Exercises
---------

- Write a version of the pred function that can only be called for argument values greater than 0.
- Write a version of the pred function that returns an option nat value "in the usual way"
- Write a tail function that can only be called with a non-empty list, using our "by cases" notation for function definition. It should look like tail'. Note 1: Where a proof value is required, you can always use tactic mode to construct the required proof, in a begin..end block. If such a proof is a single tactic long, you can write by <tactic>. For example, try by contradiction as the *result* when your new tail function is applied to an empty list. Here's how I wrote the function type. You should provide the cases (on l). Here's the type: def tail {α : Type} : ∀ (l : list α), (l ≠ list.nil) → list α. 
TEXT. -/

-- QUOTE:
-- implement the function, no need to (do not try) to match on α
-- it's named before the colon and is global to this definition
-- we do want to match (do case analysis) on l, so it's after :
-- def tail {α : Type} : ∀ (l : list α), (l ≠ list.nil) → list α 
-- |
-- |
-- QUOTE.

/- TEXT: 
Solutions
---------
TEXT. -/

-- QUOTE:
-- let's implement a "safe" pred function using tactics
def pred' : ∀ (n : nat), (n ≠ nat.zero) → ℕ :=
begin
assume n,
cases n with n',
assume h,
contradiction,
assume h,
exact n',
end

#reduce pred' 5 _
#reduce pred' 2 _
#reduce pred' 0 _

-- here's the same predecessor function presented differently
def pred'' : ∀ (n : nat), (n ≠ nat.zero) → ℕ 
| nat.zero h := by contradiction
| (nat.succ n') h := n'
 
-- a different safe predecessor function using an option return 
def pred''' : nat → option nat  
| nat.zero := option.none
| (nat.succ n') := some n'

-- the same ideas work for safe head and tail functions on lists
universe u
def tail : ∀ {α : Type u} (l : list α), (l ≠ list.nil) → list α  
| α list.nil p := by contradiction
| α (h::t) p := t  

-- apply tail to [1,2,3] giving the proof as a tactic script
#eval tail [1,2,3] 
begin 
assume p,
contradiction,
end

-- cleaner this way
#eval tail [1,2,3] (by contradiction)
#eval tail [2,3] (by contradiction)
#eval tail [3] (by contradiction)
#eval @tail nat [] (by contradiction)      -- no can do!

-- let's try it with a tactic script
#eval @tail nat [] 
begin 
assume h,   -- we're stuck, and that's good!
end


-- append: the list analog of natural number addition
-- please do compare/contrast list.append and nat.add
def appnd {α : Type} : list α → list α → list α
| list.nil m := m
| (h::t) m := h::appnd t m 

#eval appnd [1,2,3] [4,3,2]

-- QUOTE.