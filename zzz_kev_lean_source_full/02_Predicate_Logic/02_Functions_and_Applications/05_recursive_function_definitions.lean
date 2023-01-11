

/-
You should (almost must) use this "by cases" syntax
to define functions recursive functions. If you use
other syntax, you'll find that you won't be able to
have the function body call the function itself.
-/

/-
Here is the mathematical definition of the factorial
function as expressed in the particular syntax of the
Lean Prover.
-/
def factorial : ℕ → ℕ           -- remember, no := here
| 0 := 1
| (n' + 1) := (n' + 1) * factorial n'

/-
It's a recursive function definition as the return value
for n-1 is computed as part of the process of computing
the return value for the argument, n.
-/

/- 
You might be tempted to use (n-1) as the argument to the
recursive call. That won't work. The problem is that this
is a function application expression (whereas nat.succ n
is a very particular kind of application), and Lean can't
tell whether it'll always be "smaller than n". If it were
not, the recursion could go "open loop" and not terminate.
-/
def factorial2 : ℕ → ℕ           -- remember, no := here
| 0 := 1
| n := n * factorial2 (n-1)     -- can't prove termination

/-
The problem with the preceding code, for reasons we
can't get into deeply yet, is thatLean can't tell that
the argument to factorial2 will decrease in value on 
each recursive call, because all it sees is a function 
(subtraction) applied to n. Lean doesn't try to analyze
the result, at all. On the other hand, if n is of the
form (n' + 1), i.e., > 0, Lean knows that n' is one
nat.succ application smaller than n. If n is the 
argument into the function and it calls itself with
n', the function is certain to terminate for any 
finite argument (as all values of all inductively 
defined types are). Termination of all function calls
in turn is required for all functions to be "total"
and that in turn is required for the unification of
logic and programming in Lean.  It's a price but not
a terrible price to pay for such a magical thing!
-/

#eval factorial 5



