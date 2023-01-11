/-
The #eval command in Lean asks Lean
to actually evaluate an expressions
and report the result. You can also
use #reduce.
-/

#eval 1 + 1
#eval string.length "Hi there!"
#check string.length 
#reduce 1 + 1
#reduce string.length "Hi there!"

/-
From the Lean Reference Manual: As a result, 
#eval is more efficient than #reduce, and 
can be used to execute complex programs. In
contrast, #reduce is designed to be small 
and reliable, and to produce type-correct 
terms at each step. If eval "hangs" or runs
out of memory or has a recursion problem,
use #reduce.  
-/