
#check list

/-
inductive list (T : Type u)
| nil : list
| cons (hd : T) (tl : list) : list
-/

-- notations for writing cons applications
-- let's construct the list [1, 2, 3]
def three_list_nat'' :=
  list.cons 
    1
    (
      list.cons
        2
        (
          list.cons
            3
            list.nil
        )
    )

#reduce three_list_nat''

-- notation, :: is infix for cons
-- [] notation adds nil at end
def three_list_nat''' := 1::2::3::list.nil
def three_list_nat'''' := [1,2,3]


-- list prepend analogous to nat increment
def prepend' (α : Type) (a : α) (l : list α) :=
  list.cons a l

def three_list_nat' :=
  prepend' nat
    1
    (prepend' nat
      2
      (prepend' nat
        3
        list.nil
      )
    )

#eval three_list_nat'

def prepend {α : Type} (a : α) (l : list α) :=
  list.cons a l

def three_list_nat :=
  prepend 
    1
    (prepend
      2
      (prepend
        3
        list.nil
      )
    )

-- yay, that looks good
-- but know that to which it desugars

example := prepend' nat 2 [3,4,5]
#eval prepend' nat 2 [3,4,5]

example := prepend 2 [3,4,5]
#eval prepend 2 [3,4,5]

#eval 2::[3,4,5]

def tail' : ∀ {α : Type}, list α → list α 
| α list.nil := list.nil 
| α (h::t) := t

#eval tail' [1,2,3,4,5]

def head'' : ∀ {α : Type}, list α → option α 
| α list.nil := none
| α (h::t) := some h

#eval head'' [1,2,3]
#eval @head'' nat []

def head' : ∀ {α : Type} (l : list α), (l ≠ list.nil) → α 
|  α l p := 
begin
cases l,
contradiction,
exact l_hd,
end 

#eval head' [1,2,3] 
begin
contradiction,
end



/-
- Write a version of the pred function that can only be called for argument values greater than 0.
- Write a version of the pred function that returns an option nat value "in the usual way"
- Write a tail function that can only be called with a non-empty list, using our "by cases" notation for function definition. It should look like tail'. Note 1: Where a proof value is required, you can always use tactic mode to construct the required proof, in a begin..end block. If such a proof is a single tactic long, you can write by <tactic>. For example, try by contradiction as the *result* when your new tail function is applied to an empty list. Here's how I wrote the function type. You should provide the cases (on l).
def tail {α : Type} : ∀ (l : list α), (l ≠ list.nil) → list α 
-/

-- implement the function, no need to *do not try) to match α
-- it's named before the colon and is global to this definition
-- we do want to match (do case analysis) on l, so it's after :
def tail {α : Type} : ∀ (l : list α), (l ≠ list.nil) → list α 
|
|
