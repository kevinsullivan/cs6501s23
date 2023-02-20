/- TEXT:
***********
Quantifiers
***********

Among which are quantifiers over types giving rise to
parametric polymorphism, where the type of element that
is handled by an operation can vary with no changes in
the definition of the operation itself.
TEXT. -/

/- TEXT:

Quantifiers
-----------

The quantifiers are ∀ and ∃. 

Inference Rules
---------------

The inferences rules for ∀ are the same as for →. 

To prove ∃ (x : T), P x, you apply exists.intro to
two arguments: a specific value, x, of type T, and 
a separate proof of P t. We'll discuss the elimination
rule soon. 
TEXT. -/




