/- TEXT:

Suppose we know that *add 0 n' = n'*
and that we want to prive that *add 0 (succ n')
= (succ n')*. Key insight: We can apply the 
*second* axiom of addition,given by the second 
rule in its definition, to rewrite the term, 
*add 0 (succ n')* to the term *succ (add 0 n');*
then we can use the fact that (by assumption) 
0 is a left 0 for n' to rewrite the term 
*succ (add 0 n')* to *succ n'.* That's it. 
We've shown that 0 + succ n' = succ n'.

But what could possibly justify assuming 
that 0 + n' = n' in the first place? Well,
let's see if it can be justified informally
before getting into formalities.

Let's start by noting that by the first rule 
of addition, 0 is a left zero for 0. This
proof gives us a base on which we can now
construct a proof that 0 is a left zero for 1. 

Details: we want to show that 0 + 1 = 1. That 
is, we want to show that 0 + succ 0 = succ 0. 
By the second rule/axiom of add, the left side 
is succ (0 + 0). *BE SURE YOU UNDERSTAND THIS
STEP.*  Now yy the first rule, 0 + 0 = 0, so 
we can rewrite succ (0 + 0) to just succ 0. 
With this expression on the left side, all 
that remains to prove is that succ 0 = succ 0,
and this is true of course by the reflexivity 
of the equality relation. 

To recap, we proved a "base case" (that
zero is a left identity for zero) using the 
first axiom of addition. Then we applied the
second axiom to show that 0 is a left identity
for 1. With this proof in hand we can apply
the second axiom *again* to construct a proof
that zero is left identity for 2. From this
we can derive that 0 is a left identity for
3. Indeed to prove that 0 is a left identity
for *any* n, we start with a proof that it's 
a left identity for zero using the first
axiom, then we iteratively apply the second
axiom n times to prove it's a left identity
for *any* n. 

Let's just program it to make it all clear.
Out program will take any value n and return
a proof that 0 is a left identity for it. It
does this in the reverse order, constructing
a proof for the case where n is non-zero, i.e.,
where n = succ n' for some n', and obtaining 
a proof for n' *by recursion*. The recursive
calls implement iteration until the base case
of n = 0 is reached, at which point a proof
for that case is returned, the recursion
unwinds, and we're left with a proof that 0
is a left identity for that arbitrary n. The
existence of this function shows that we can
construct a proof of the proposition that 0
is a left identity for any n, and so it is
true *for all* n. And that's what we wanted.
QED. 
TEXT. -/

-- QUOTE: 
-- a proof-returning function defined by cases
-- takes any n and returns a proof of 0 + n = n
def zero_left_ident_n : ∀ n, (nat.add 0 n = n)
| nat.zero := by simp [nat.add] -- base case
| (nat.succ n') :=              -- recursive case
  begin 
  simp [nat.add],               -- applies second rule and ...
                                -- removes succ on each side
                                -- by injectivity of constructors
                                -- inherent in inductive definitions
  exact (zero_left_ident_n n'), -- prove result recursively 
  end 

