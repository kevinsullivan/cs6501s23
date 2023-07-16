/- TEXT:

===========
Typeclasses
===========

The previous chapter has taught you about proof by induction. Our 
need for this proof construction method was created by our need for  
proofs of some basic properties of all natural numbers: namely,
for any *a*, *0* is both a left and a right identity; and for any 
*a, b,* and *c,* that *a + b + c = (a + b) + c*. (As application
is left associative we omit explicit parentheses in *(b + c)*.)

The need for these proofs in turn was driven by our need to specify
what it means to be a monoid, so that we could pass values of a 
*monoid* type, rather than separate *operator* and *identity* 
arguments, to our higher-order function, *foldr.

In this chapter we complete our solution to the problem of passing
arguments that are required to have specific algebraic properties. 
We'll take monoids again as a simple, driving example. 

Key ideas include the following: (1) we will define a safe version 
of  *foldr* that wil works for any monoid; we'll see how to associate
monoid data (a binary operation, identity element, property proofs)
with types, whose values are taken as monoid elements; (4) how to 
tell Lean to automatically (implicitly) find and pass monoid data 
structures to functions depending on the types of other arguments;
(5) and ways to use this approach in useful ways. 
TEXT. -/
