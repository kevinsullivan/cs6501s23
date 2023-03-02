

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


def sub2 : nat → nat 
| nat.zero := nat.zero
| (nat.succ nat.zero) := nat.zero
| (nat.succ (nat.succ n')) := n'
