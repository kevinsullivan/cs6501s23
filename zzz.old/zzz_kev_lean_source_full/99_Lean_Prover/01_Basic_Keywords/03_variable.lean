/-*** variable ***-/

/-
The variable command in Lean declares a new variable an it's type
without binding a value to it. 
-/

variable seven : ℕ 
variable some_data_type : Type
variable a_silly_proposition : ∀ (P : Prop), true

-- def a_silly_proposition := begin assume P, exact true.intro end

/-
You can use #check to check the types of such variables
-/

#check seven                -- it's type is nat
#check some_data_type       -- it's type is Type
#check a_silly_proposition  -- it's type is ∀ (P : Prop), true

/-
We can tell whole logical stories just using variables and their types
-/

variable Person : Type    -- Person is some data type
variable Likes : Person → Person → Prop -- Likes is a 2 argument predicate
variables (Mary Margo : Person)  -- p and q are variables of type Person
variable likes_mary_margo : Likes Mary Margo -- likes_mary_margo is a proof of Likes Mary Margo

/-
We've basically assumed that likes_mary_margo is bound to (has as its value) 
a proof of Likes Mary Margo. We can see that Lean's type checker thinks so, too.
-/
def proof_mary_likes_margo : Likes Mary Margo := likes_mary_margo -- good proof, it typechecks
def bad_proof : Likes Mary Margo := true.intro -- bad proof, type checker catches it!



-- Another in-class example

variable even : ℕ → Prop 

#check even 5
#check even 6

def even (n : ℕ) := n%2 = 0

#check even 5


