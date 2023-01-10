import tactic.ring
import tactic.norm_num

namespace cs2120f22

/-
We now launch into the final major topic of this
course: induction principles and how they enable
both the definition of recursive functions and
the construction of proofs "by induction." 
-/

/-
Key ideas #1: 

Every inductively defined data type comes with 
its own induction axiom. If you learned about
"proof by mathematical induction" in high school
or another course, you were learning how to use
the induction axiom for *natural numbers*, but
you can also use induction to reason about all
values of *any* inductively defined data type.

#2: If a type is named T, then T.rec_on is the 
name of the corresponding induction axiom *in 
Lean*. The statement of the inducation axiom,
however, even in Lean, is purely mathematical
and is independent of Lean. It's part of the
logic we're learning. The idea of an induction
axiom is general.

#3. An induction axiom is an axiom for proving 
*universal generalizations* (∀ propositions) 
that assert that something is true for *all* 
values of a given type.

#4. If a type has only enumerated values 
(like bool has only tt and ff) the induction
axiom is equivalent to case analysis. You
need to prove that each individual value of
a type has a given property.

#5. If a type is "recursive", in which case
some constructors build "bigger" values of a
type from smaller values of the same type
(e.g., as nat.succ takes a nat, n', and yields
the nat (succ n'), incorporating the smaller
value/object into the larger one), the you
will have more complex induction axioms. In
general these will be of the following form:

(1) Show that each base/non-recursive value
has the given property
(2) For each recursive constructor, show that
if you apply it to smaller values that already
have the given property, then the larger ones
you construct will have that property, too.

In proofs by induction on a natural number,
you'll have two cases: an easy one for the
base case, zero, and a more complex one for
the inductive case, where you'll have to show
that for any n', if n' as the property then
so does (succ n'). 

The same ideas hold for the list type (as we 
discuss in the extra credit section, below).
Finally, at the very end of this file, we
sketch out how these ideas apply to design
and reasoning about programming languages.
-/

/- ************************************
INDUCTION OVER ALL VALUES OF TYPE bool
************************************ -/

/-
As an example, let's look again at the definition
of the bool type, and then at its induction axiom.
The lesson will be that induction on bool amounts
to simple case analysis, with two cased. If we 
show that both ff and tt have a given property,
then we've shown that *all* values of the bool
type have it, as there are no other values than
these two.
-/


/- 
Here's the definition of the bool type

inductive bool    -- data type definition
| ff : bool       -- first constructor
| tt : bool       -- second constructor
-/

/- Here's the induction axiom for bool.
Be sure you understand it! Note that the
use of "motive" for the name of a property
might be a little confusing. Just think of
it as "P" if that helps. 
-/
#check @bool.rec_on
/-
bool.rec_on : 
  Π {motive : bool → Sort u_1} 
  (n : bool), 
  motive ff → 
  motive tt → 
  motive n

Let's decode that:
(0) bool.rec_on is an axiom that says that:
(1) for any *property or function* taking ...
(2) any arbitrary Boolean value, n,
(3) if you prove that ff has the property
(4) and you prove that tt has the property
(5) then you've given either a proof for each
    possible n or a return value for each n,
    and so have either proved a generalization
    or have defined a total function
-/

/-
Key idea #4 again: For simple types like bool, 
whose values are enumerated, proof by induction
is just proof by case analysis. That's what the 
rule for bool says: to prove that all bools have
a property (motive) it suffices to that ff has
it and that tt has it.  

As a reminder, here's a proof that for any
bool, n, the negation of the negation of n is n.
The idea is just to show it's true for each of
the values individually. 
-/
example : ∀ (n : bool), bnot (bnot n) = n :=
begin
assume n,
cases n,
exact rfl,
exact rfl,
end 

/-
Here's a proof of the same proposition by the
application of the induction axiom for bool.
-/
example : ∀ (n : bool), bnot (bnot n) = n :=
begin
-- let n be an arbitrary bool avlue
assume n,

-- apply the induction principle
apply bool.rec_on n,
/-
Note that the first *explict* argument
to bool.rec on is an arbitrary bool. We
can thus apply the principle to n, in
which case the remaining things to be
proved are motive tt and motive ff, the
"motive" being the property that "bnot 
(bnot n) = n." That is, we must prove
this proposition first for n = f and 
then for n = ff
-/
exact rfl,  -- easy
exact rfl,  -- easy
-- QED
end  

/-
Now applying the induction axiom directly
isn't the preferred way to do it in Lean.
Rather, use the induction tactic. It sets
up the cases you need to prove.
-/

example : ∀ (n : bool), bnot (bnot n) = n :=
begin
assume n,
induction n,
exact rfl,  -- proof of case n = ff
exact rfl,  -- proof of case n = tt
end

/-
Another way to think about the induction
principle for bool is that it provides a
means for implementing functions that take
any natural number as input. Suppose we
want to define a function that takes any
bool argument and that returns 0 for ff
and 1 for tt. Let's build this function
by applying the induction principles to
two such machines.
-/

def answer_for_ff := 0
def answer_for_tt := 1

def bool_to_bit (b : bool) : nat := 
  bool.rec_on 
  b 
  answer_for_ff 
  answer_for_tt

-- Test cases. It works!
example : bool_to_bit ff = 0 := rfl
example : bool_to_bit tt = 1 := rfl

/-
We can do the same thing with the induction
tactic.
-/

def bool_to_bit' (b : bool) : nat := 
begin
induction b,
exact 0,
exact 1,
end 

-- Test cases. It works!
example : bool_to_bit' ff = 0 := rfl
example : bool_to_bit' tt = 1 := rfl


/-
Take-away #1: For an enumerated type, such
as bool, we can build a proof that all values
of this proof have a given property. We do
this by applying the induction axiom to two
smaller "machines" each of which gives a 
proof for the corresponding bool input value.
Such a proof is basically a function that takes 
any bool and returns a proof for that value.

Take-away #2: For an enumerated type, such
as boolol, we can also build a *function* that
takes any value of this type and returns a
corresponding result value. To build such 
a function, we apply the induction axiom
to the return values for each of the possible
argument values.  

In either case, we apply the induction axiom
to proofs/values for each possible argument
value to obtain a machine that when given any
argument value returns the correct corresponding
proof or function value.  
-/

/-
EXERCISE: (1) define a data type called
day, the values of which are the (names
of) the days of the week. (2) Define a 
function, next_day : day → day, that if
given a day returns the next day of the
week, and define prev_day : day → day, 
that when given a day returns the previous
day. (3) Give a proof *by induction* of
the proposition that for any day, today, 
the day after yesterday is again today.
-/


#check @nat.rec_on
/-
Π {motive : ℕ → Sort u_1} 
  (n : ℕ), 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) → 
  motive n
-/

/-
We now turn to the more interesting case of
the definition of the ℕ data type and *its* 
corresponding induction principle.
-/

open nat 
/-
inductive nat       -- data type definition
| zero              -- zero is a value of this type
| succ (n : nat)    -- given n : ℕ, succ n is also a ℕ

This data type is defined truly inductively.
It provides a constructor for "laying down a
ground floor" and it provides a constructor
that, "when placed on any floor, n'"" builds 
the "next floor up," for n = (succ n').
-/

def z := zero             -- first constructor
def one := succ z         -- second
def two := succ (succ z)  -- second
def two' := succ one      -- second
def three := succ (two)   -- second
def four := succ (succ (succ (succ zero)))

/-
Okay, now that we've got the ℕ data type
defined, let's define some functions on 
this type to precisely mimic (you could
even say, "to specify") basic arithmetic
functions.
-/


/-
increment -- given n', return n = n' + 1
-/
def inc (n' : ℕ) : ℕ := succ n'

-- it works!
#eval inc three
example : inc three = four := rfl


/-
decrement 

We define this function by case analysis on
an argument, n. If n is zero, we return zero.
Otherwise, if n = (succ n') we return n'. This
is a beautifully simple example of how we can
use pattern matching to "destructure" n into
(succ n'), then returning n'.
-/
def dec : ℕ → ℕ
| zero := zero
| (succ n') := n'

#eval dec 4 
#eval dec 0 

/-
How about a function for adding two natural
numbers, n and m. Now we get to see recursion
in action! We define n + m  to be n in case
m is zero, and otherwise n + (m' + 1) to be
1 + (n + m'), where (n + m') is computed by 
a call to the same addition function!
-/

#check nat.add

def my_add : ℕ → ℕ → ℕ 
| n 0 := n
| n (succ m') := succ (my_add n m')

-- a few test cases -- seems to work!
example : my_add 5 0 = 5 := rfl
example : my_add 5 3 = 8 := rfl


/-
Just as our implementation of addition
uses succ to add 1 to n "m times", we
can implement multiplication by adding
n to itself m times.
-/
def my_mul : ℕ → ℕ → ℕ 
| n 0 := 0
| n (succ m') := my_add n (my_mul n m') 

-- test cases
example : my_mul 7 0 = 0 := rfl
example : my_mul 7 1 = 7 := rfl
example : my_mul 7 5 = 35 := rfl

/-
And exponentiation multiplies n by itself
m times.
-/
def my_exp : ℕ → ℕ → ℕ 
| n 0 := 1
| n (succ m') := my_mul n (my_exp n m') 

-- test cases
example : my_exp 2 0 = 1 := rfl
example : my_exp 2 1 = 2 := rfl
example : my_exp 2 4 = 16 := rfl


/-
-/

#check @nat.rec_on
/-
  Π {motive : ℕ → Sort u_1} 
  (n : ℕ), 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) → 
  motive n
-/

/-
So now we'll see how we can "build"
recursive functions by applying the
induction axiom for natural numbers
to "two smaller machines", one that
gives an answer for argument zero and
one that, if given n' and the answer
for n', combines them to produce the
answer for n = n'+1. It will be a
lot easier to see the idea in action
with a unary function, taking just
one natural number argument. For this
example, we'll pick the factorial
function. Here it is as we'd usually
define it in Lean.
-/
def factorial : ℕ → ℕ 
| nat.zero := 1
| (nat.succ n') := my_mul (succ n') (factorial n')
-- parenthesize constructor expressions

-- it works
example : factorial 0 = 1 := rfl
example : factorial 5 = 120 := rfl
example : factorial 6 = 720 := rfl

/-
Yeah, now for the fun part. We will first
build two "machines." The first gives the
answer for n = 0. The second, given n' and
the answer for n' returns the answer for 
n' + 1. For example, suppose you want to 
compute the answer for n = 6. It's easy 
to compute if you know n' = 5 and that the 
answer for factorial n' is 120. To get the
answer for n = n' + 1 = 6, you multiply 
(n' + 1) = (5 + 1) by the factorial of n',
which is 120, to get the answer, 720, for
n = n' + 1 = 6. With these two machines, y
should be able to compute the factorial of
n for any n: run the first machine to get 
the answer for n' = 0, then pass n' and 
the answer for n' to the second machine to
get the answer for 1, then repeat that as
many times as needed to get the answer for
whatever n you want!  
-/

-- a "machine" returns factorial 0 
def fac_zero := 1

/-
A machine that when given n' and factorial
n' returns factorial of n' + 1.
-/
def fac_step 
  (n' : nat)     -- what floor you're on
  (n'_fac : ℕ)   -- answer for that floor
  := (n'+1) * n'_fac

/-
Applying the "step" machine to 5 and the
factorial of 5 (120) should return the
factorial of 6. And it does. 
-/

example : fac_step 1 1 = 2 := rfl     -- fac 2
example : fac_step 5 120 = 720 := rfl -- fac 6



def factorial' (n : nat) : nat := 
  nat.rec_on 
    n         -- given arbitrary n
    fac_zero  -- given the answer for n = 0
    fac_step  -- given function for computing the next the given n and factorial n the answer for  factorial n+1


-- It works! Yay!
example : factorial' 0 = 1 := rfl
example : factorial' 1 = 1 := rfl
example : factorial' 2 = 2 := rfl
example : factorial' 3 = 6 := rfl
example : factorial' 4 = 24 := rfl
example : factorial' 5 = 120 := rfl


/-
Let's see again how this work in terms of
the induction axiom for natural numbers.
Here's the axiom again.

  Π {motive : ℕ → Sort u_1}
  (n : ℕ), 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) → 
  motive n

(1) Sort u_1, the "return type", is ℕ
(2) The n here is the argument to factorial'
(3) motive 0 = factorial' 0 = fac_zero = 1
(4) now see how our step function works
    (a) (Π (n : ℕ), motive n → motive n.succ)
    (b) it takes n, a nat, and motive n = factorial n
    (c) and it returns motive n+1 = factorial n+1

Applying the induction axiom to these arguments
yields a machine that given n return motive n = 
factorial' n *for any n whatsoever*. In a sense,
the big machine iterates application of the step
function as many times as needed, starting with
the value for the base case, to produce the value
that is sought!

So now we see how to explain the induction
principle in English. To produce a function
that can return a value (or if the return type
is a proposition in Prop, a proof that that
proposition) for *any* n, all you need to 
provide are (1) a machine returning a proof
for the base case of n = zero, and a machine,
the "step" function, that when given n' and
the correct result for n', return the result
for n' + 1.

When it comes to proofs of propositions about
all natural numbers, what you need to provide
is a proof for 0 and a proof that for any n',
if there's a proof for n' then there's a proof
for n' + 1. You just need to define how to get
a proof for n' + 1 *given the assumption that
you know n' and have a proof for n'. That is
proof by induction for the natural numbers,
also sometimes called proof by "mathematical"
induction.

What's amazing is that this technique will 
work just as well for lists, trees, programs,
or any other inductively defined data types as
it does for nat (albeit with different smaller
machines that need to be defined).
-/

/-
EXERCISE: Define a function that sums up all
the natural numbers from 0 to any given natural
number, n.
-/

def sum_to : ℕ → ℕ 
| 0 := 0
| (succ n') := (succ n') + sum_to n'

example : sum_to 0 = 0 := rfl
example : sum_to 5 = 15 := rfl
example : sum_to 10 = 55 := rfl

/-
Formulate property that you will then want
to prove holds for all natural numbers.
-/

def sum_property (n : ℕ) := 2 * sum_to n =  n * (succ n)


/-
The proposition
-/

def the_proposition := ∀ n, sum_property n

/-
Prove that the property holds for 0
-/

lemma sum_zero : sum_property 0 := eq.refl 0 

/-
Prove that if it holds for n' then it holds for n'+1
-/

lemma sum_n' (n' : ℕ) (ind_hyp : sum_property n'): 
  sum_property (succ n') :=
begin
  unfold sum_property,
  -- 2 * sum_to n'.succ = n'.succ * n'.succ.succ
  unfold sum_to,
  ring,
  unfold sum_property at ind_hyp,
  rw ind_hyp,
  ring,
end


/-
Put the "small machines" together using induction axiom
-/
example : the_proposition :=
  λ n, 
    nat.rec_on    -- apply induction axiom
    n               -- to an arbitrary n
    sum_zero        -- a proof of base case
    sum_n'          -- a proof of step/inductive case
/-
And have now is a "big machine" that, given *any*
n (base case or otherwise), produces a proof that
that (arbitrary) n has the sum_property. This is
thus a proof that every natural number has that
property, which is what we wanted to prove. 
-/

/-
-/
example : the_proposition  :=
begin

unfold the_proposition,


-- let n be an arbitrary natural number
assume n,

-- unfold definition of sum_property
unfold sum_property, 

-- the proof is by induction on n
induction n with n' pf_n',

-- constructing a proof for the base case is easy
-- rfl alone would do but let's go step bf step
{ 
  unfold sum_to, 
  exact rfl,
},

/-
Now we have to provide a proof for the inductive 
case. The crucial thing to see here is that Lean
has already *assumed* that n' is a nat and that
you have a proof for n'. These are of course just
the "inputs" to the "inductve" machine. If it
isn't clear, look at the second line of the proof
of sum_n' above. Here, Lean is automating that 
step of the proof for you. Key idea: when doing
a proof by induction on a ℕ, in the second step
you *assume* you're given both n' and a proof for
n' (the "induction hypothesis"), and you have to
then construct a proof for n'+1. This is how it
works!
-/
{ 
  -- expand definitions: sum_property and sum_to
  unfold sum_to,
  -- normalize/simplify algebra (distributive law)
  ring,
  -- KEY! rewrite goal using induction hypothesis!
  rw pf_n',
  -- now just push through the rest of the algebra
  ring,
},
-- QED
end 

/-
EXERCISE: Look at our definition of my_add. What
it does is give you the axioms for addition! It
says for any n, adding n and zero is n, and that
adding n and (succ m) [the case where the second
argument, m', is greater than 0], reduces to "one 
more than adding n and m'. Sum of n and m' here
is *assumed* to be available, and in practice is 
computed by a recursive call to my_add. We can
be assured that the recursion will terminate, as
the value of the second argument goes down by 1
on each recursive call, and will eventually (in 
a finite number of steps) reach the based case.

So now suppose you want to prove that for any
n, my_add n 0 = n. This is super-easy because
it's just an axiom by our definition of my_add.
-/

example : ∀ n, my_add n 0 = n :=
begin
assume n,
unfold my_add,
end

/-
On the other hand, we have no axiom that tells
us that for any n, 0 + n = n (with 0 on the left
instead of on the right). This fact we will have
to prove---by induction. This is an exercise that 
you will carry out by constructing the smaller
proofs separately then combining them using the
induction axiom for ℕ, and then by using the
induction tactic in Lean.
-/

/- A. 
Formally specify the *property* of a natural 
number that you will then want to assert holds
for all natural numbers. This will be a predicate
on a natural number, n. Call it left_zero_add.
-/

def left_zero_add (n) : Prop := 0 + n = n

/-
Now construct separate proofs that (a) 0 has
this property, (b) if arbitrary n' has it then
so does succ n', and (c) that by the induction
axiom *all* natural numbers therefore have this
property. Call your proofs left_zero_zero,
left_zero_add_n, with the complete proofs being
called left_zero and left_zero'. Note the extra 
"my" in the last name -- to avoid conflicts 
with a result already in the Lean library.
-/

-- base case
theorem left_zero_add_zero : left_zero_add 0 :=
begin
-- unfold the definition, rfl applied automatically 
unfold left_zero_add,
end

/- inductive case

Assume that n' is arbitrary that that you're
given a proof for n' (that 0 + n' = n'), then
with these inputs construct a proof for n' + 1
(that 0 + succ n' = succ n').
-/
theorem left_zero_add_n' : 
  ∀ n', 
    left_zero_add n' →
    left_zero_add (n' + 1) :=
begin
-- expand definition
unfold left_zero_add,
-- assume given n' and proof for n',
assume n' ind_hyp,
/-
Now construct proof for n' + 1

First, use associativity of addition
to rewrite 0 + (n' + 1) as (0 + n') + 1.
Next use ih to rewrite this as n' + 1!
That gives n' + 1 = n' + 1, which is easily
proven the by reflexivity of equality, which 
the rw tactic applies for us. 

Here's what the add_assoc theorem from the
Lean library proves:

add_assoc : ∀ a b c, a + b + c = a + (b + c)

Here we use this proven equality to rewrite the
goal from right (in the equality) to left. We
don't expect you to know the theorems proved in
the libraries. But you should clearly understand
how we're using this theorem in this proof.
-/
rw<-add_assoc,
/-
We've now finagled the goal into a form in
which we can apply the induction hypothesis
to rewrite it into a form we can finally prove.
-/
rw ind_hyp,
end

/-
If you want the proof of this ∀ theorem to 
look even more like a function, move the 
assumptions of n' and left_zero_add n' to
the left of the colon. That's it!
-/

theorem left_zero_add_n'' 
  (n' : ℕ) 
  (ih : left_zero_add n' ) : 
  left_zero_add (n' + 1) :=
begin
unfold left_zero_add at ih,
unfold left_zero_add,
rw<-add_assoc,
rw ih,
end


/-
Now that we've defined our base and step
"machines" (lemmas), we assemble them into
an overall proof by applying the induction
axiom to them.
-/
theorem left_zero : ∀ n, 0 + n = n :=
begin
assume n,
exact 
  nat.rec_on 
    n 
    left_zero_add_zero 
    left_zero_add_n',
end


/-
EXTRA CREDIT MATERIAL REVIEWED IN DETAIL ONLINE 12/7
-/

namespace hidden

/-
We define list as a *polymorphic* data type (just
like in Java), with two constructors. Given α, a
list of α objects is *either* empty (nil) or it is
constructed (cons) from a new element, h, of type 
α, and a 1-smaller list of α elements, t. The "h"
argument is said to be the element at the "head" 
of the new list, while the smaller list t, is said
to be the "tail" of the new list.
-/

inductive list (α : Type) : Type
| nil : list
| cons (h : α) (t : list) :list


/-
Here we define two lists of natural numbers.
-/
def l : list ℕ :=   -- the list [1,2,3]
  list.cons         -- takes two arguments as follow
    1               -- head element
    (list.cons      -- tail list
      2             -- head element
      (list.cons    -- tail list
        3           -- head element
        list.nil    -- tail list (base case)
      )
    ) 

def m : list ℕ :=     -- the list [4,5,6]
  list.cons 
    4 
    (list.cons 
      5 
      (list.cons 
        6 
        list.nil
      )
    ) -- [1,2,3]

/-
Note that the list type (beyond being polymorphic)
is very similar to the nat type. The nil constructor
is analogous to nat.zero, while the cons constructor
is analogous to nat.succ. 

The difference: nat.zero takes a single smaller nat, 
n', as an argument and forms the term (succ n') to
represent a one-larger-than-n' natural number. By
contrast, list.cons takes two arguments. The smaller 
list argument, t, is analogous to n'. The h argument 
is new. The constructor forms the term, (cons h t),
representing the list with the new element, h, at
its head, and the given argument, t, as the rest of
the new list. Be sure you can see exactly how the
preceding example lists are formed, l and m, bigger
lists being formed from a head *element* and a tail 
*list*. 
-/

/-
Not only are the list and nat types analogous, but 
also the basic functions we define on them. Here,
for example, is a function for appending one list,
l, to another list m. If for example l = [1,2,3] 
and m = [4,5,6], then (appnd l m) = [1,2,3,4,5,6].

The function works by recursion on l. Compare with
nat.add. If the first argument, l, is the empty 
list (nil), we just return the second list. This
is analogous to our rule for adding n and 0. On
the other hand, if l is non-empty (like non-zero),
then it must be of the form (cons h t), where h
is the first element of l and t is the remaining
sublist. In this case, the return value of appnd
is the list with h at its head and (recursively!)
(appnd t m) as its tail. 

For example with l = [1,2,3] and m = (4,5,6) for
(appnd l m) we get (cons 1 (appnd [2,3],[4,5,6])).
-/

def appnd {α : Type} : list α → list α → list α 
| list.nil m := m
| (list.cons h  t)      m      := list.cons h (appnd t m)
--           1::[2,3]  [4,5,6]    1::[2,3,4,5,6] 

/-
Appending nil and m gives m (see first rule of appnd)
-/
example : appnd list.nil m = m := rfl -- yay

#check nat.add
/-
Indeed, we can easily prove that this rule holds
for all m, just we we showed that n + 0 = n is
true for all n. In both cases, these rules are
true because they're *axioms* of add and append,
respectively, defined by the first cases in each
of the function definitions. The "simp [appnd]"
tactic simplifies the goal using the definition
of appnd.
-/
theorem nil_is_left_zero_for_lists {α : Type}: ∀ m : list α, appnd list.nil m = m := by simp [appnd] 


/-
Here's a test case for (appnd [1,2,3] [4,5,6]), using
Python-like notation for lists in this comment.
-/
example : 
  appnd l m = 
  (list.cons 
    1 
    (list.cons 
    2 
    (list.cons 
      3 
      (list.cons 
        4 
        (list.cons 
          5 
          (list.cons 
            6 
            list.nil
          )
        )
      )
    )
    )
  ) := rfl    -- yay, success


/-
I was asked whether we could prove the ∀ proposition
"by induction." Yes, we can, but we don't really need
induction in this case. But here it is anyway.
-/
example : ∀ {α : Type} (m : list α), appnd list.nil m = m :=
begin
assume α m,
induction m with h t,
-- base case
exact rfl,
-- inductive case
exact rfl,
--simp [appnd],
end  

/-
Now for the main point of this whole example. You will 
recall from studying the previous material that while
it was easy to prove ∀ n, n + 0 = n, it was harder to
prove ∀ n, 0 + n = n. In fact, we really needed to use
induction to prove it. There's no rule in the definition
of add that takes care of this case.

Similarly, while it was easy to prove that "nil is a 
left zero" for append, it's harder to prove it's a
right zero, because our definition of appnd doesn't
have a rule for that case. Once again we need to use
induction.
-/

example : ∀ {α : Type} (s : list α), appnd s list.nil = s :=
begin
-- assume we're given a list, s, of elements of type α 
assume α s,
show appnd s list.nil = s,

induction s with h t,


/-
The base case is taken care of by the first axiom of appnd
(this is a case where s, the first argument, is nil).
-/
exact rfl,

/-
The inductive case depends completely on the induction
hypothesis. Look at the induction hypothesis. We need
to manipulate the goal into a form where we can use the
induction hypothesis to rewrite it into a form that we
can finally "finish off." 

So let's look at at the goal:

appnd (list.cons h t) list.nil = list.cons h t. Now you
have to look at the definition of appnd, and see if/how
you can simplify parts of it. Look at the left-hand side:
(appnd (list.cons h t) list.nil). The second appnd rule
lets us can rewrite this as (list.cons h (appnd t nil)).
So now our goal is (cons h (appnd t nil)) = cons h t;
and look at that! The sub-term (appnd t nil) mathches
the left side of the induction hypothesis, so we can
use it to further rewrite the goal as (cons h t)),
leaving us with cons h t = cons h t as the remaining
goal, easily proved by the fact that equality is a
reflexive relation. Lean actually takes care of a 
few of the intermediate reasoning steps automatically,
so all have to do in this case is ask Lean to simplify
the goal using the definition of appnd, then rewrite
using m_ih, and Lean takes care of applying rfl itself.
-/
simp [appnd],
rw s_ih,
end  

end hidden

/-
Discussion. Now let's compare and contrast the 
induction axioms for nat and list respectively.
Note that we're now working directly with Lean
definitions of these types (being outside of the
hidden namespace). 
-/

#check @nat.rec_on 
/-
Π {motive : ℕ → Sort u_1} 
  (n : ℕ), 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) 
  → motive n

In English, given any property (motive) of
natural numbers and an arbitrary natural
number n, to show that n has the property,
motive, it will suffice to show 

(1) 0 has it (you have a proof of motive 0)
(2) if whenever an arbitrary n' has it, then
n'+1 has it, too.

The intuition again is that if these two
facts are true, then you can construct a
proof of motive n for any n by constructing
a proof for zero, then applying the second
inductive rule to construct a proof for each
succeeding number all the way up to n. As 
n was arbitrary, the induction proof works
for *any* (and thus for all) n.
-/

/- 
Now let's look at the list induction axiom.
Compare and contrast closely with that for
nat. 
-/
#check @list.rec_on
/-
Π {T : Type u_2} 
{motive : list T → Sort u_1} 
(n : list T), 
motive list.nil → 
(Π (hd : T) (tl : list T), motive tl → motive (hd :: tl)) → 
motive n

This rule says the following. If you have any
type, T (the list element type, as list is now
a polymorphic type), and any property of lists
of Ts, and if n is an arbitrary list, to show
that n has the property (motive) is will suffice
to show that:

(1) nil has the property 
(2) for any list tl and any element hd, if tl
has the property, then (cons h tl) has it too.
The :: syntax is just infix notation for cons. 
-/

/-
As a final sketch, we define a type whose
values are outlines of imperative programs.
This definition says that a program is

(1) empty OR
(2) an assignment statement (we omit the 
variable and expression parameters), OR
(3) a sequential composition of smaller 
programs: (p1 ; p2) in C, where semicolon
means "sequential composition, i.e., run
p1 then in the resulting context run p2."
(4) OR a condition "if (b) then run tb 
else run fb", OR
(5) while (b) run the smaller body program

We leave the boolean conditions out to
keep things simple.
-/

inductive program : Type
| empty
| assignment 
| seq (p1 p2 : program)
| if_ (tb fb : program)
| while (body : program)

open program

/-
Here's a little program in the programming
language we just defined!
-/
def my_program := 
  seq 
    (assignment)
    (while 
      (
        seq assignment assignment
      )  
    )

  /- This is a more realistic version

  X := v;
  while () {
    Y := 2;
    Z := X + 1
  }
  -/

/-
What's the point? The point is that 
our program type has an induction rule.
If we ever wanted to show that every
program in a given language has a 
certain property, we could use proof
by induction! Note however, that we
no longer have to prove just a base
case and *one* inductive case; we have
to prove a base case (for empty) and
an inductive case for each remaining
constructor! In each case we assume
that the smaller programs we're given
have the given property, and will need
to show that applying the constructor
used to build a larger program yields
a program that still has the property.
-/

#check @program.rec_on

/-
EXERCISE: Express this induction rule
in English. 
-/

end cs2120f22
