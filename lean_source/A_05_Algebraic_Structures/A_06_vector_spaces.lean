import .A_03_group_actions
import algebra.add_torsor

/- TEXT: 

************************
Fields and Vector Spaces
************************

Introduction
------------

A module of actions, with addition, subtraction, and
scalar multiplication, with scalars from a ring, such
as ℤ, becomes a vector space when its scalar ring is
in fact a field. That roughly requires that there be
multiplicative inverses of scalars. 

A lack of division is exactly what makes ℤ a ring and 
not a field. On the other hand ℝ\\{0} is a field, with 
the usual addition, subtraction, and multiplication, but 
now also multiplicative inversion, thus division, and 
also fractions. 

One can take any fraction of a vector, but not of a 
symmetry rotation. Our symmetry rotations do form a
module, but not a vector space. Vector spaces unlike
modules have all *fractions of actions* as well. 
TEXT. -/