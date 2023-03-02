

#check nat

/-
The definition of the type, nat, the terms/values of which we
use to represent natural numbers.

inductive nat
| zero : nat
| succ (n : nat) : nat

The set of terms is defined inductively. First, *zero* is a term
of type *nat*. Second, if *n'* is any term of type *nat*, then so
is *nat.succ n'* (which you can also write as n'.succ or n' + 1).
-/

-- notations for writing succ applications
def three'  := (nat.succ (nat.succ (nat.succ (nat.zero))))
def three  := nat.zero.succ.succ.succ




-- increment is just succ application 
def inc (n' : nat) : nat := n'.succ
def three'' := inc(inc(inc nat.zero))

/-
A predecessor (one less than) function can be defined by 
case analysis on a nat argument. Here we'll define *pred'*
to return 0 when applied to 0, and otherwise to return the
one smaller value, *n'*, when applied to any non-zero value,
*nat.succ n'*. 

Rather than "implementing a function" think "proving a function 
type." A "proof" of function type, *nat → nat,* is any function 
that converts any given nat into some resulting nat. 

When proving a function or other data type, as opposed to a 
logical (proposition) type, is that *any* proof will do to prove
the proposition, while we usually want a specific function of the
specified type. Here, for example, we don't want any function
that takes and returns a nat, but one that in particular returns
the required answer (one less than the argument).

Differences between proofs of propositions are irrelevant in
Lean. Differences between "proofs" of function or other data
types aren't irrelevant; they're usually highly relevant! So 
be sure to construct a preferred "proof" of any given function
type.

Let's look at the predecessor function: the one that takes any
nat value and returns the following: zero if the argument is 
zero, and otherwise n', where the argument value is n'+1. 
-/
def pred' : nat → nat :=
begin
assume n,
cases n with n',  -- this is right now
exact 0,
exact n',
end 

-- quick test
#eval pred' 6
example : pred' 6 = 5 := rfl

/-
Here's the same function just specified
using pattern matching notation (which,
as we've seen generalizes case analysis). 
 -/
def pred : nat → nat 
| nat.zero := nat.zero  -- loop at zero
| (nat.succ n') := n' 

#eval pred 5
example : pred 5 = 4 := rfl

/-
Pattern matching generalizes case analysis
by giving you a means to return different
results based on deeper analysis of argument
structures using pattern matching/unification.
-/
def sub2 : nat → nat 
| nat.zero := nat.zero
| (nat.succ nat.zero) := nat.zero
| (nat.succ (nat.succ n')) := n'

