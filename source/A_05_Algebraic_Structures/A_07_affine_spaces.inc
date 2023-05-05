
*************
Affine Spaces
*************

Under Construction. 

`affine_space <https://leanprover-community.github.io/mathlib_docs/linear_algebra/affine_space/basic.html>`_

In this section we'll make sense of the statement that an 
affine space is just a torsor whose action/difference set
is not just a group or module but a vector space. That means
we can add and subtract actions and we have scalar multiplication
by fractional scalars. Differences between torsor points will
now be vectors in a vector space, which operate on points, 
in turn, additively, by *translating* them. 

In Lean, *affine_space V P*, where *V* is the type of
vectors and P is the torsor of points, is just another 
notation for *add_torsor V P* where the action set, V, 
will have the structure of a vector space.  

.. code-block:: lean

  -- See: they're the same. 
  
  #check @add_torsor
  /-
  add_torsor : 
    Π (G : out_param (Type u_1)), 
      Type u_2 → 
    Π [_inst_1 : out_param (add_group G)], 
      Type (max u_1 u_2)-/
  
  open_locale affine
  #check affine_space
  /-
  affine_space : 
    Π (G : out_param (Type u_1)), 
      Type u_2 → 
    Π [_inst_1 : out_param (add_group G)], 
      Type (max u_1 u_2)
  -/

More to come. 
