

#check nat

/- TEXT
The definition of the type, nat, the terms/values of which we
use to represent natural numbers.

inductive nat
| zero : nat
| succ (n : nat) : nat

The set of terms is defined inductively. First, *zero* is a term
of type *nat*. Second, if *n'* is any term of type *nat*, then so
is *nat.succ n'* (which you can also write as n'.succ or n' + 1).

-- notations for writing succ applications
def three'  := (nat.succ (nat.succ (nat.succ (nat.zero))))
def three  := nat.zero.succ.succ.succ



-- increment is just succ application 
def inc (n' : nat) : nat := n'.succ
def three'' := inc(inc(inc nat.zero))


def pred' : nat → nat :=
begin
assume n,
cases n with n',  
exact 0,  -- when n is zero
exact n', -- when n is succ n'
end 

-- quick test
#eval pred' 6
example : pred' 6 = 5 := rfl


def pred : nat → nat 
| nat.zero := nat.zero  -- loop at zero
| (nat.succ n') := n' 

#eval pred 5
example : pred 5 = 4 := rfl



-- this example illustrates pattern matching
-- for more fine-grained case analysis
def sub2 : nat → nat 
| nat.zero := nat.zero
| (nat.succ nat.zero) := nat.zero
| (nat.succ (nat.succ n')) := n'

-- addition increments the second argument
-- the first argument number of times
def plus : nat → nat → nat
| nat.zero m := m
| (nat.succ n') m := nat.succ (plus n' m)

#eval plus 3 4

-- multiplication adds the second argument
-- to itself the first argumen number of times
def times : nat → nat → nat
| 0 m := 0
| (n'+1) m := plus m (times n' m)

#eval times 5 4
#eval times 1 20


-- substraction illustrates case analysis on 
-- multiple (here two) arguments at once
def subtract :  nat → nat → nat
| 0 _ := 0
| n 0 := n
| (n' + 1) (m' + 1) := subtract n' m'

#eval subtract 7 5
#eval subtract 7 0
#eval subtract 5 7
#eval subtract 0 7


-- exponentiation is multiplication of the second
-- argument by itself the first argument number of times
def power : nat → nat → nat
| n nat.zero := 1
| n (nat.succ m') := times n (power n m')

-- a few test cases
example : power 2 0 = 1 := rfl
example : power 2 8 = 256 := rfl
example : power 2 10 = 1024 := rfl
