
def Q (n : nat) := n = n
#check Q  -- "propositions are types"


-- Q n is a type (proposition) dependent on n
#check Q 0
#check Q 1
#check Q 2


-- A function from n : ℕ to *proofs (values)* of *Q n*
def dep_func_prop (n : ℕ) : Q n := begin unfold Q end


#check dep_func_prop

#check dep_func_prop 0
#check dep_func_prop 1
#check dep_func_prop 2

#reduce dep_func_prop 0
#reduce dep_func_prop 1
#reduce dep_func_prop 2

variables 
  (α : Type)          -- a *data* type
  (P : α → Prop)      -- predicate on α   

#check ∀ (a : α), P a
#check Π (a : α), P a
