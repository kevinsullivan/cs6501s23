/-
Finally we implement the function using a Java
style of syntax.
-/
namespace impl_cstyle

def sub1 (n : ℕ) : ℕ :=   -- first arg named to left of :
  match n with            -- match does case analysis after all
  | 0 := 0
  | (n' + 1) := n'
  end

def add2 (n : ℕ) := n+2   -- n+2 is short for succ(succ n)!

/-
Our tests suggest our functions are working yet again.
-/
example : sub1 0 = 0 := rfl
example : sub1 1 = 0 := rfl
example : sub1 2 = 1 := rfl
example : sub1 3 = 1 := rfl  -- bad test
example : add2 0 = 2 := rfl
example : add2 1 = 3 := rfl
example : add2 2 = 4 := rfl
example : add2 3 = 6 := rfl -- bad test

end impl_cstyle


/-
Next we define functions that implement 
Boolean  "and." Note that in each case we 
"pattern match" on both arguments.
-/

def my_bool_and : bool → bool → bool 
| tt tt := tt
| tt ff := ff
| ff tt := ff
| ff ff := ff

/-
Evaluation of this "cases" syntax
is, again, in top-to-bottomorder: 
if the arguments match the first 
pattern (tt tt), this function return 
the value expressed to the right of
that := (tt). If the arguments don't
match the first pattern, Lean moves
on to the next, until a match is found
and the corresponding result is returned. 
Lean will tell you if you've forgotten 
a possible combination of argument 
values. Try it by commenting out one
of the cases. 
-/


/-
A nice property of this syntax is that the 
truth table for "Boolean and" is as clear as 
day. That said, after the first of the rules, 
the rest all return false. You can use the 
"wildcard" character, _ (underscore) in Lean 
to match any value to avoid having to write
the three rules separately.
 -/

def my_bool_and2 : bool → bool → bool 
| tt tt := tt
| _ _ := ff

/-
Maybe at this point you're not sure that these
two functions have exactly the same meaning. 
Let's check that by stating the proposition 
that they return the same values for all of
the possible combinations of argument values,
and proving it. The proof is by case analysis
on the possible values of the arguments.
-/

example : 
  ∀ (b1 b2 : bool), 
    my_bool_and b1 b2 = 
    my_bool_and2 b1 b2 
  :=
begin
assume b1 b2, -- bind argument names

-- case analysis on b1 
cases b1,     

-- b1 false

-- case analysis on b2
cases b2,
-- b2 false 
apply rfl,
-- b2 true
apply rfl,

-- b1 true

-- case analysis on b2
cases b2,
-- b2 false
apply rfl,
-- b2 true
apply rfl,
end 

/-
Here are test cases
-/
example : my_bool_and tt tt = tt := rfl
example : my_bool_and tt ff = ff := rfl
example : my_bool_and ff tt = ff := rfl
example : my_bool_and ff ff = ff := rfl


/-
Functions in Lean must be "total," which means that
they must be defined to return values of the right
types for *all* possible combinations of arguments.
If you delete cases from the my_bool_and definition
you'll get a missing cases error and the following
evaluations will "block" on the undefined cases. Try
it!
-/
