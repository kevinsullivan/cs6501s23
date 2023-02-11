
/- 2. TEXT:
So let's get started as if we were in CS1, with
a few simple examples of functions from the Lean
libraries imported by default when Lean starts up.
Let's look at string.length, the standard function
in Lean for returning the length of any given string.
-/

#check string.length
#check string.length "CLIC!"  -- "CLIC!".length works
#eval string.length "CLIC!"   -- There's the actual length



example : string.length "CLIC!" = 5 := rfl

