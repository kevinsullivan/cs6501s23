
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

def tail : ∀ {α : Type}, list α → list α 
| α list.nil := list.nil 
| α (h::t) := t

#eval tail [1,2,3,4,5]

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

