
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


def map_string_bool : (string → bool) → list string → list bool 
| f list.nil := list.nil 
| f (h::t) := f h::map_string_bool f t

-- is_even takes a nat and return tt if it's even else ff
def is_even (n : nat) : bool := n % 2 = 0
#eval is_even 2
#eval is_even 3


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
#eval fold_nat' nat.add 0 zero_right_id_add [1,2,3] -- good
#eval fold_nat' nat.add 1 zero_right_id_add [1,2,3] -- not good



def n_ary_add := fold_nat' nat.add 0 zero_right_id_add

-- It seems to work!
#eval n_ary_add []            -- zero arguments
#eval n_ary_add [5]           -- one argument
#eval n_ary_add [4,5]         -- two arguments
#eval n_ary_add [1,2,3,4,5]   -- five arguments, etc!


def n_ary_mul := fold_nat' nat.mul 1 sorry
#eval n_ary_mul [1,2,3,4,5]



-- Problem #1
/-
Let's do some test-driven development here. 
(1) Define function type
(2) Write (initially failing) test cases
(3) Complete implementation and expect test cases to pass
-/
def n_ary_append {α : Type} : list (list α) → list α
| [] := []
| (h::t) := h ++ n_ary_append t


-- test cases for 0, 1, 2, and more arguments
example : @n_ary_append nat [] = [] := rfl
example : n_ary_append [[1,2,3]] = [1,2,3] := rfl
example : n_ary_append [[1,2,3],[4,5,6]] = [1,2,3,4,5,6] := rfl
example : n_ary_append [[1,2,3],[4,5,6],[7,8,9]] = [1,2,3,4,5,6,7,8,9] := rfl

-- Problem #2
def sum_lengths {α : Type} : list (list α) → nat
| [] := 0
| (h::t) := (list.length h) + (sum_lengths t)

example : @sum_lengths nat [] = 0 := rfl
example : sum_lengths [[1,2,3]] = 3 := rfl
example : sum_lengths [[1,2,3],[4,5,6]] = 6 := rfl
example : sum_lengths [[1,2,3],[4,5,6],[7,8,9]] = 9 := rfl

-- Problem #3 
def even_lengths {α : Type} : list (list α) → bool
| [] := tt
| (h::t) := (is_even (list.length h)) && (even_lengths t)

example : @even_lengths nat [] = tt := rfl
example : even_lengths [[1,2,3],[4,5,6],[7,8,9]] = ff := rfl
example : even_lengths [[1,2,3,4],[4,5,6],[7,8,9]] = ff := rfl
example : even_lengths [[1,2,3,4],[4,5,6,7],[7,8,9,0]] = tt := rfl



def all_even' : list ℕ → bool
| list.nil := tt
| (h::t) := band (is_even h) (all_even' t)   -- band is &&

-- Seems to work
#eval all_even' [2,4,6,8]
#eval all_even' [1,4,6,8]


def all_even_op : nat → bool → bool
| n b := (is_even n) && b

def all_even : list nat → bool
| list.nil := tt
| (h::t) := all_even_op h (all_even t)

-- seems to be working
#eval all_even []       -- expect tt
#eval all_even [1]      -- expect ff
#eval all_even [0,2,4]  -- expect tt
#eval all_even [0,2,5]  -- expect ff


def foldr {α β : Type} : (α → β → β) → β → (list α) → β 
| op id [] := id
| op id (h::t) := op h (foldr op id t)

#check @foldr

def all_even_yay : list nat → bool := foldr all_even_op tt

#check all_even_yay


#eval all_even_yay []       -- expect tt
#eval all_even_yay [1]      -- expect ff
#eval all_even_yay [0,2,4]  -- expect tt
#eval all_even_yay [0,2,5]  -- expect ff


#eval foldr nat.add 0 [1,2,3,4,5] 
#eval foldr nat.mul 1 [1,2,3,4,5] 

def any_true : list bool → bool := foldr bor ff 

#check nat.add

example : ∀ n : nat, nat.add n 0 = n := 
begin
assume n,
by simp [nat.add],
end


example : ∀ n : nat, nat.add 0 n = n := 
begin
assume n,
simp [nat.add],   -- nope, no rule matches the goal
end


example : ∀ n : nat, nat.add 0 n = n := 
begin
assume n,
cases n with n',  -- nope, no rule matches the goal
simp [nat.add],   -- base case is easy
                  -- but now we're stuck
end


