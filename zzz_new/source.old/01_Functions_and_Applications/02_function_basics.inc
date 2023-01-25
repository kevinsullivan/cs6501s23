************
Basics
************

.. code-block:: lean

  #check string.length
  #check string.length "CLIC!"  -- "CLIC!".length works
  #eval string.length "CLIC!"   -- There's the actual length


In predicate logic, a function application 
can be thought of an an expression that names 
another object: it's return result. For example,
the expression (string.length "CLIC!"), serves
as another expression/name for 5. They're equal,
as we can even now state and prove formally.

.. code-block:: lean

  example : string.length "CLIC!" = 5 := rfl

