Π Types
-------

.. code-block:: lean

  
  -- A predicate (function from value to type)
  def Q (n : nat) := 
    ∃ m, m = n.succ
  
  -- A function from (n : ℕ) to *proof* of proposition *about n*
  def dep_fun_prop : ∀ (n : ℕ), Q n :=
  begin
  intro n,
  apply exists.intro (n.succ) _,
  apply eq.refl (n+1),
  end
  
  -- The type of the result depends on the argument *value*
  #check dep_fun_prop
  
  #check dep_fun_prop 0
  #check dep_fun_prop 1
  #check dep_fun_prop 2
  
  #reduce dep_fun_prop 0
  #reduce dep_fun_prop 1
  #reduce dep_fun_prop 2
  
  
  variables 
    (α : Type)          -- a *data* type
    (P : α → Prop)      -- predicate on α   
  
  #check ∀ (a : α), P a
  #check Π (a : α), P a
  

