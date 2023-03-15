
example {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) := 
begin
assume pq qr,   -- assume P → Q and Q → R
assume p,       -- to show P → R, assume p a proof of P
exact qr (pq p) -- and derive the desired proof of R
end


example {α β γ : Type} : (α → β) → (β → γ) → (α → γ) :=
begin
assume αβ βγ,   -- assume f g
assume a : α,   -- assume a
exact βγ (αβ a) -- return λ a, g (f a)
end


def comp {α β γ : Type} (f : α → β) (g : β → γ) : α → γ :=
fun (a : α), g (f a)


def inc (n : ℕ) := n + 1
def sqr (n : ℕ) := n * n
def inc_then_sqr := comp inc sqr
example : inc_then_sqr 5 = 36 := rfl   -- seems to work!


def inc_then_sqr' := sqr ∘ inc        -- composition!
example : inc_then_sqr' 5 = 36 := rfl -- seems to work!


#eval list.length [1,2,3] -- apply length function to list
#eval [1,2,3].length      -- function application notation
#eval nat.pred 3          -- apply decrement function to 3

-- Apply composition of length and pred to list
#eval (comp list.length nat.pred) [1,2,3] 
#eval (nat.pred ∘ list.length) [1,2,3]




def inc_list_nat : list nat → list nat 
| list.nil := list.nil  
| (h::t) := (inc h)::inc_list_nat t

-- it works
#eval inc_list_nat[]        -- expect []
#eval inc_list_nat [1,2,3]  -- expect [2,3,4]



def sqr_list_nat : list nat → list nat 
| list.nil := list.nil 
| (h::t) := (sqr h)::sqr_list_nat t

-- It works
#eval sqr_list_nat [1,2,3,4,5]


def any_list_nat : (nat → nat) → list nat → list nat 
| f list.nil := list.nil 
| f (h::t) := f h::any_list_nat f t

-- It seems to work!
example : any_list_nat sqr [1,2,3,4,5] = [1,4,9,16,25] := rfl    
example : any_list_nat inc [1,2,3,4,5] = [2,3,4,5,6] := rfl
example : any_list_nat nat.pred [1,2,3,4,5] = [0,1,2,3,4] := rfl


#eval any_list_nat string.length ["I", "Love", "Math"]  -- nope!


def xyz_list_nat : (string → nat) → list string → list nat 
| f list.nil := list.nil 
| f (h::t) := f h::xyz_list_nat f t

-- It seems to work
#eval xyz_list_nat string.length ["I", "Love", "Math"]

/-
But we run into the same problem as before if we now want
to map lists of strings to Boolean values, e.g., reflecting
whether the length of each string is even (tt) or not (ff).
Cloning code and editing it to produce another special case
is really not the best solution.
-/
def map_string_bool : (string → bool) → list string → list bool 
| f list.nil := list.nil 
| f (h::t) := f h::map_string_bool f t

-- is_even takes a nat and return tt if it's even else ff
--
def is_even (n : nat) : bool := n % 2 = 0
#eval is_even 2
#eval is_even 3

/-
Now we can map a function that tells whether a given string
is of even length or not over any given list of strings to 
get a corresponding list of tt/ff values.
-/
def is_even_length := is_even ∘ string.length
#eval map_string_bool is_even_length ["I", "Love", "Math"]


def map_list {α β : Type} : (α → β) → list α → list β 
| f list.nil := list.nil
| f (h::t) := f h :: map_list f t

-- It seems to work!
#eval map_list nat.succ [1,2,3]
#eval map_list is_even_length ["I", "Love", "Math"]



def reduce_sum : list nat → nat
| list.nil := 0
| (h::t) := nat.add h (reduce_sum t)

#eval reduce_sum []           -- sum of zero arguments
#eval reduce_sum [5]          -- sum of one argument
#eval reduce_sum [5,4]        -- sum of two arguments
#eval reduce_sum [5,4,3,2,1]  -- sum of five arguments


def reduce_prod' : list nat → nat
| list.nil := 0
| (h::t) := nat.mul h (reduce_prod' t)

#eval reduce_prod' [3,2,1]   -- expect 6 got 0!

/- 
To see what goes wrong, let's unroll the recursion:
- reduce_prod' [3,2,1] =
- mul 3 (reduce_prod' [2,1]) =
- mul 3 (mul 2 (reduce_prod' [1])) =
- mul 3 (mul 2 (mul 1 (reduce_prod' []))) =
- mul 3 (mul 2 (mul 1 0)) = 0!
The problem is now clear, and so is the solution:
we need to return a different value for the base
case of an empty list when the binary operation is
multiplication rather than addition. Specifically,
we need to return 1 rather than zero. You can now
probably guess that in general we want to return
the *identity, or neutral, value* for whatever
the binary operator is for the base case. Here
we want to return 1.
-/

def reduce_prod : list nat → nat
| list.nil := 1
| (h::t) := nat.mul h (reduce_prod t)

#eval reduce_prod []          -- expect 1
#eval reduce_prod [5,4,3,2,1] -- expect 120


def fold_nat (op : nat → nat → nat):  nat → list nat → nat
| id list.nil := id  
| id (h::t) := op h (fold_nat id t)


-- It seems to work!
#eval fold_nat nat.add 0 [1,2,3,4,5]  -- expect 15
#eval fold_nat nat.mul 1 [1,2,3,4,5]  -- expect 120



#eval fold_nat nat.mul 0 [1,2,3]  -- oops, wrong


def fold_nat' 
  (op: nat → nat → nat) 
  (id :nat) 
  (right_id : ∀ (n : nat), op n id = n) : 
  list nat → nat
| list.nil := id  
| (h::t) := op h (fold_nat' t)


theorem zero_right_id_add : ∀ (n : nat), nat.add n 0 = n :=
begin
assume n,
simp [nat.add]
end 

-- Now we can safely use fold_nat' 
#eval fold_nat' nat.add 0 zero_right_id_add [1,2,3]

-- This application fails because the proof is wrong
#eval fold_nat' nat.add 1 zero_right_id_add [1,2,3]



def n_ary_add := fold_nat' nat.add 0 zero_right_id_add

-- It seems to work!
#eval n_ary_add []            -- zero arguments
#eval n_ary_add [5]           -- one argument
#eval n_ary_add [4,5]         -- two arguments
#eval n_ary_add [1,2,3,4,5]   -- five arguments, etc!


def n_ary_mul := fold_nat' nat.mul 1 sorry
#eval n_ary_mul [1,2,3,4,5]


