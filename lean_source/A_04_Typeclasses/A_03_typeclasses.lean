import algebra.group.basic

namespace cs6501

/- TEXT: 

***********
Typeclasses
***********

The typeclass mechanism of Lean, first implemented for Haskell,
provides exactly this capability. The basic idea is that if we
annotate the add_monoid' structure definition with *[class]* we
tell Lean to in effect keep a table of monoid instance values, 
indexed by the element type α, which it can then use later on 
to look up (infer) the monoid *instance* values that should be 
passed to various applications of foldr.

Typeclass types
---------------

Rather than declaring *structure mul_monoid'* we would declare 
*@[class] structure mul_monoid*, or just *class mul_monoid*.  
TEXT. -/ 

-- QUOTE:
@[class] structure mul_monoid (α : Type) : Type := mk::
  (op : α  → α  → α )   -- data
  (e : α )              -- data
  (ident : ∀ a, op e a = a ∧ op a e = a)
  (assoc: ∀ a b c, op a (op b c) = op (op a b) c)

-- unfortunate but unavoidable duplication 
class add_monoid (α : Type) : Type := mk::
  (op : α  → α  → α )   -- data
  (e : α )              -- data
  (ident : ∀ a, op e a = a ∧ op a e = a)
  (assoc: ∀ a b c, op a (op b c) = op (op a b) c)
-- QUOTE.

/- TEXT:
Using the @[class] annotation tells Lean that we are defining
a structure whose instances are to be indexed by type values,
α. When we define an instance, we annotate it with @[instance]
or just use the *instance* keyword. 

Typeclass instances
-------------------
TEXT. -/

-- QUOTE:
@[instance] def nat_add_monoid : add_monoid nat := add_monoid.mk nat.add 0 sorry sorry -- zero_ident_add_nat nat_add_assoc  
instance list_append_monoid {α : Type} : @add_monoid (list α) := add_monoid.mk list.append [] sorry sorry 
-- QUOTE.

/- TEXT:

Instance inference
-------------------

Finally, we use *square* brackets to tell Lean to infer typeclass instances
at function application time. Here are revised versions of our foldr functions.
TEXT. -/

-- QUOTE:
def  mul_foldr {α : Type} [m : mul_monoid α] : list α → α 
| list.nil := match m with (mul_monoid.mk op e _ _) := e end
| (h::t) := match m with (mul_monoid.mk op e _ _) := m.op h (mul_foldr t) end

def add_foldr {α : Type} [m : add_monoid α] : list α → α 
| list.nil := match m with (add_monoid.mk op e _ _) := e end
| (h::t) := match m with (add_monoid.mk op e _ _) := m.op h (add_foldr t) end
-- QUOTE. 

/- TEXT: 

Safe, general foldr
-------------------

Now we can apply foldr functions without having to give explict monoid 
instance arguments.
TEXT. -/

-- QUOTE:

#eval add_foldr [1,2,3,4,5]                 -- op = nat.add
#eval add_foldr [[1,2,3],[4,5,6],[7,8,9]]   -- op = list.append
#eval mul_foldr [1,2,3,4,5]                 -- error: no instance available!


-- QUOTE. 


/- TEXT:

Type constraints
----------------

The next idea we'll make explicit is that typeclass arguments
can be used to constrain type arguments, specifically to types
for which a typeclass instance for the particular type has been
defined. To start, let's give another English reading of the type 
specification of our foldr operations. We'll take  mul_foldr as 
an example.

- def  mul_foldr {α : Type} [m : mul_monoid α] : list α → α 

We can now read this as follows: The mul_foldr operation takes
as its first (implicit) argument, any element type, α, *as long 
as α has been "imbued with" a multiplicative monoid structure.* 
Then if given a list of α elements it returns a reduced value 
of the α type. 

In other words, the requirement that there be a typeclass 
instance for α imposes a *constraint* on the *type values* 
that can be passed to foldr. You can only apply mul_foldr to 
a  list of values of type α if α has been given the structure
of a multiplicative monoid (by the definition of a suitable
monoid typeclass instance). 

Let's see what happens if we try to apply mul_foldr to a list
of values of a type, α, for which we have not yet defined a
monoid structure. As you will guess, Lean will tell us that
it can't infer a required typeclass instance. 
TEXT. -/



-- QUOTE:
instance nat_mul_monoid := 
  mul_monoid.mk nat.mul 1 sorry sorry           
instance bool_mul_monoid : mul_monoid bool := 
  mul_monoid.mk band tt sorry sorry 

#check mul_monoid
#check add_monoid
#eval mul_foldr [tt,ff,tt]
#eval add_foldr [tt,ff,tt]                      -- error: no instance


-- Exercise: define a typeclass instance to fix this error.
-- QUOTE.
/- TEXT:

Example: default typeclass
--------------------------

It'll be helpful to see a simpler typeclass and how it can be
used to help define otherwise troublesome functions. We will
define a typeclass, *default_value α*, an instance of which 
has just one field, holding a single value of type α to be
used as a default return value in function definitions in case
of exceptions. 

In particular, we'll see how to use it to write a total function
that returns the value at the head of any list of α, as long as 
there's a default_value instance for α providing an α value to
return in case one tries to compute the head of an empty list.  
TEXT. -/


-- QUOTE:
class default_value (α : Type) := mk::
(val : α)

instance nat_def : default_value nat := default_value.mk 0
instance bool_def : default_value bool := default_value.mk tt
instance list_def {α : Type} : default_value (list α) := default_value.mk []

def list_head {α : Type} [d : default_value α] : list α → α
| [] := d.val
| (h::t) := h

#eval list_head [1,2,3]                     -- returns nat
#eval list_head [ff,tt,ff]                  -- returns bool
#eval list_head [[1,2,3],[4,5,6],[7,8,9]]   -- returns list nat

#eval list_head ([] : list nat)             -- returns default nat!     
#eval list_head ([] : list bool)            -- returns default bool!

instance string_def : default_value string := default_value.mk ""

#eval list_head ([] : list string)          -- error: no default for string

-- EXERCISE: define a default_value typeclass instance to fix that error
-- QUOTE. 

/- TEXT:

Operator overloading
--------------------

The original purpose for typeclasses in Haskell was to enable
overloading of operator notations. For example, we might want 
the infix notation, *, to mean nat.mul for natural numbers but
bool.band for Boolean values. To do this is just an application
of what you now already know. Let's see.  
TEXT. -/

-- QUOTE:
-- First the typeclass
class has_mult (α : Type) :=    -- has_mul in Lean; also "dropping mk::"
(op : α → α → α)

-- Then an overloaded operator; applies right version of op for α 
def mult {α : Type} [has_mult α] (a b : α) := has_mult.op a b

instance has_mult_nat : has_mult nat := has_mult.mk nat.mul
instance has_mult_bool : has_mult bool := has_mult.mk band

#eval mult 3 4
#eval mult tt tt
#eval mult ff tt
#eval mult tt ff
#eval mult ff ff

-- Now all we need is a notation

notation (name := mult) a ` * ` b := mult a b

#eval tt * ff     -- this works well
#eval 2 * 3       -- oops, * already overloaded, thus *ambiguous*

-- QUOTE. 

/- TEXT:
Typeclass inheritance
---------------------

Typeclass "interface inheritance" can be used to define complex 
typeclasses as compositions of simpler ones. To see an example, 
let's look at the actual definition of (multiplicative) monoid
in the Lean libraries. To use the monoid typeclass we have to
import the library in which it's defined. Note that at the top
of this file we're now importing algebra.group. To figure out
what library to import, use the online Lean mathlib reference.
TEXT. -/

-- QUOTE:

#check monoid         -- extends semigroup, mul_one_class
#check semigroup      -- extends has_mul
#check has_mul        -- as we've seen
#check mul_one_class  -- extends has_one 
#check has_one        -- arbitrary value called "one"


#check group


-- See documentation for how it all fits together. 

-- QUOTE. 

end cs6501

