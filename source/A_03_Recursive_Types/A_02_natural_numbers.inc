***************
Natural Numbers
***************

Data Type
---------

.. code-block:: lean

  #check nat


.. code-block:: lean

  -- notations for writing succ applications
  def three'  := (nat.succ (nat.succ (nat.succ (nat.zero))))
  def three  := nat.zero.succ.succ.succ

Operations
----------

Having seen how the *nat* data type is defined, we now look 
at how to define functions taking *nat* values as arguments.
As we've seen before, many such functions here will again be
defined by case analysis on an incoming nat argument value. 
That means considering two cases separately: the incoming value
is either zero or non-zero: that is, either *nat.zero,* or 
*nat.succ n'* for some "one-smaller" value, *n'*. For example,
if the incoming argument is *succ(succ(succ zero))*, i.e., 3, 
then (a) it does not match *nat.zero*, but (b) it does match 
*nat.succ n'*, with *n'* is bound to *succ(succ zero)*, i.e., 2.

.. code-block:: lean

  -- increment is just succ application 
  def inc (n' : nat) : nat := n'.succ
  def three'' := inc(inc(inc nat.zero))

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

.. code-block:: lean

  def pred' : nat → nat :=
  begin
  assume n,
  cases n with n',  
  exact 0,  -- when n is zero
  exact n', -- when n is succ n'
  end 
  
  -- quick test
  #eval pred' 6
  example : pred' 6 = 5 := rfl

Here's the same function just specified
using pattern matching notation (which,
as we've seen generalizes case analysis). 

.. code-block:: lean

  def pred : nat → nat 
  | nat.zero := nat.zero  -- loop at zero
  | (nat.succ n') := n' 
  
  #eval pred 5
  example : pred 5 = 4 := rfl

Pattern matching generalizes case analysis
by giving you a means to return different
results based on deeper analysis of argument
structures using pattern matching/unification.

.. code-block:: lean

  def sub2 : nat → nat 
  | nat.zero := nat.zero
  | (nat.succ nat.zero) := nat.zero
  | (nat.succ (nat.succ n')) := n'

