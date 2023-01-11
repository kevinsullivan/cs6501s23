/- *** functons involving nats *** -/

/-
In the field of natural number arithmetic, one
of the fundamental functions is called successor.
In Lean it's nat.succ in Lean. It's the function
that, when applied to any nat, returns its successor,
the next larger nat. For example, the application
expression, (nat.succ 0), means 1, while the term,
nat.succ(nat.succ 0) means 2. (There are some
subtleties that we'll open up later.)
-/

example : nat.succ 0 = 1 := rfl


/-
Question: What is the type of nat.succ? Figure it
out first, then you may check your answer by using 
#check.
-/


/- *** syntax options for defining your own funtions *** -/

/-
Firat we'll see how to implement basic Boolean functions,
such as "and." For a value of this type, there are just two
cases: tt and ff (in Lean). Then we'll turn to functions 
involving natural numbers, where for any natural number,
there are still just two cases but they are now n = 0 and
n > 0.
-/

/-
We will also use this discussion to present a few different
styles you can use to define functions in Lean. We wil in
particular implement two simple functions using each of three
different syntactic approaches. The functions, sub1, and add2,
respectively, return the predecessor, and the successor of the
successor of their arguments.

- sub1 : ℕ → ℕ 
    Given n, 
      case analysis:
        when n is 0, return 0,              -- case n = 0
        when n is (nat.succ n'), return n'  -- case n > 0

- add2 : ℕ → ℕ 
    Given n, 
    return nat.succ(nat.succ n))
-/

/-
First, we'll see how we can define these
functions by declaring their types and then
using *tactic scripts* to produce correct 
implementations: values of these function
types that compute and return the correct
results. It feels like you're just proving
a theorem, but now the proof is a program!
that implements your task.
-/
namespace impl_script

/-
To start, we'll declare each function just 
as we'd state a logical proposition, then
we'll "prove" they type by providing not
any program of this type but one that also
does what we require. Here we go.
-/


def sub1 : ℕ → ℕ :=
  begin
  -- give argument a name
  assume n,       
  -- do case analysis on n (=0, >0)
  cases n with n',
  -- case where n = 0
  exact 0,
  -- case where n = (succ n') > 0
  exact n',
  end


def add2 : ℕ → ℕ :=
  begin
    assume n,   -- bind name to argument
    exact n+2,  -- means exactly nat.succ(nat.succ n)
  end


/-
Next we can show that we can apply these
functions and that they work as expected.
-/
example : sub1 0 = 0 := rfl
example : sub1 1 = 0 := rfl
example : sub1 2 = 1 := rfl
example : sub1 3 = 1 := rfl  -- bad test
example : add2 0 = 2 := rfl
example : add2 1 = 3 := rfl
example : add2 2 = 4 := rfl
example : add2 3 = 6 := rfl -- bad test

end impl_script



/-
Next we'll implement the same functions using
Lean's "pattern matching" or "by cases" syntax.
-/
namespace impl_cases

def sub1 : ℕ → ℕ 
  | 0 := 0                -- if arg is 0, then 0
  | (nat.succ n') := n'   -- otherwise one less than arg


/-
Each line starting with | gives a pattern-result
pair. Each line is |, pattern, := result. The really
fundamental idea here is that you can pull apart the
arguments while you're matching to get at value that
they incorporate. Starting from the top, Lean matches
given arguments with each pattern until one matches.
The matching process can bind names to parts of the
arguments. These names can then be used on the right
of the := to define the value of the return result. 
-/  

/-
The "patterns" that we try to match with the incoming
argument in our examples here correspond to the two
cases, n = 0 and n > 9. These are the only two forms
of a nat, so this is all the cases we have to consider.
To the right of the := are the answers. Here, if the 
argument of an application is 0, the function returns
0. Otherwise n > 0, and in this case it can only be 
of the form (nat.succ _), where the _ is the term
that represents the natural number one smaller than
n. 
-/

/-
The add2 function, next, is very simple.
-/

def add2 : ℕ → ℕ := 
  fun n, nat.succ (nat.succ n) 

/-
Remember how to read a lambda (function) expression.
This definition says that add2 is a function that 
takes a nat and returns a nat (that's its type), and
in particular is "the function that when given n as
an argument, applies nat.succ to it twice and returns
that value. 
-/

/-
Our tests suggest our functions are working.
-/
example : sub1 0 = 0 := rfl
example : sub1 1 = 0 := rfl
example : sub1 2 = 1 := rfl
example : sub1 3 = 1 := rfl  -- bad test
example : add2 0 = 2 := rfl
example : add2 1 = 3 := rfl
example : add2 2 = 4 := rfl
example : add2 3 = 6 := rfl -- bad test

end impl_cases


/-
Finally we implement the same two functions again using 
a Java style of syntax.
-/
namespace impl_cstyle

def sub1 (n : ℕ) : ℕ :=   -- first arg named to left of :
  match n with            -- match in Leandoes case analysis
  | 0 := 0                -- n = 0
  | (n' + 1) := n'        -- n > 0
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
A new idea you've been seeing in the preceding discussion
is called "destructuring."

Consider the sub1 function. If the argument, n, is zero, 
it just returns zero. If the argument is not zero (given
that it must be of type nat) there's no possibility (we
are telling you) for n other than that is the successor
of some other natural number. Even if that other is zero,
is is still 1, and so n > 0.

The way we'll represent a natural number, n, is either as
a term, zero, or as some number of nested applications of
nat.succ to zero. succ(succ(0)) for example represents 3.

Now suppose the argument, n = 3. That's just shorthand for
n = succ (succ (succ 0)) Now look at the second pattern in
our function definitions. It matches when is is of the form
(nat.succ _), where the _ is also a nat value, thus either
zero or (nat.succ _), eventually bottoming out in a zero.

The pattern is (n' + 1), shorthand for (succ n'). Now
let's see what happens when we match (or "unify") it with
the actual argument value, 3, or succ (succ (succ 0)):

    (succ (succ (succ 0)))
    (succ n')

The result ihere is that (1) the pattern matches, and (2)
the name, n', is bound to (succ (succ 0)). Note that if 
you plug that in for n' in the pattern you get exactly the
argument value, 3. We've thus got that n' = 2 in this case,
and that's exactly one less than three, which is just what
we wanted.
-/