/- 2. Some basics

So let's get started as if we were in CS1, with
a few simple examples of functions from the Lean
libraries imported by default when Lean starts up.
Let's look at string.length, the standard function
in Lean for returning the length of any given string.
-/

#check string.length
#check string.length "CLIC!"  -- "CLIC!".length works
#eval string.length "CLIC!"   -- There's the actual length



/- In predicate logic, a function application 
can be thought of an an expression that names 
another object: it's return result. For example,
the expression (string.length "CLIC!"), serves
as another expression/name for 5. They're equal,
as we can even now state and prove formally.
-/

example : string.length "CLIC!" = 5 := rfl


