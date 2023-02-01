

example : nat.succ 0 = 1 := rfl





namespace impl_script



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

example : sub1 0 = 0 := rfl
example : sub1 1 = 0 := rfl
example : sub1 2 = 1 := rfl
example : sub1 3 = 1 := rfl  -- bad test
example : add2 0 = 2 := rfl
example : add2 1 = 3 := rfl
example : add2 2 = 4 := rfl
example : add2 3 = 6 := rfl -- bad test

end impl_script



namespace impl_cases
def sub1 : ℕ → ℕ 
  | 0 := 0                -- if arg is 0, then 0
  | (nat.succ n') := n'   -- otherwise one less than arg


/-  TEXT:
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

/-  TEXT:
The add2 function, next, is very simple.

def add2 : ℕ → ℕ := 
  fun n, nat.succ (nat.succ n) 

/-  TEXT:
Remember how to read a lambda (function) expression.
This definition says that add2 is a function that 
takes a nat and returns a nat (that's its type), and
in particular is "the function that when given n as
an argument, applies nat.succ to it twice and returns
that value. 

/-  TEXT:
Our tests suggest our functions are working.
example : sub1 0 = 0 := rfl
example : sub1 1 = 0 := rfl
example : sub1 2 = 1 := rfl
example : sub1 3 = 1 := rfl  -- bad test
example : add2 0 = 2 := rfl
example : add2 1 = 3 := rfl
example : add2 2 = 4 := rfl
example : add2 3 = 6 := rfl -- bad test

end impl_cases


/-  TEXT:
Finally we implement the same two functions again using 
a Java style of syntax.
namespace impl_cstyle

def sub1 (n : ℕ) : ℕ :=   -- first arg named to left of :
  match n with            -- match in Leandoes case analysis
  | 0 := 0                -- n = 0
  | (n' + 1) := n'        -- n > 0
  end

def add2 (n : ℕ) := n+2   -- n+2 is short for succ(succ n)!

/-  TEXT:
Our tests suggest our functions are working yet again.
example : sub1 0 = 0 := rfl
example : sub1 1 = 0 := rfl
example : sub1 2 = 1 := rfl
example : sub1 3 = 1 := rfl  -- bad test
example : add2 0 = 2 := rfl
example : add2 1 = 3 := rfl
example : add2 2 = 4 := rfl
example : add2 3 = 6 := rfl -- bad test
end impl_cstyle


/-  TEXT:
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
