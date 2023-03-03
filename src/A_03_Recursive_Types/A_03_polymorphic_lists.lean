
#check list


namespace poly_lists

universe u
inductive list (T : Type u)
| nil : list
| cons (hd : T) (tl : list) : list
end poly_lists

-- example: let's represent the list of nats, [1,2,3]
def three_list_nat'' :=
  list.cons   -- takes two arguments
    1         -- head of new list
    (         -- tail list of the new list 
      list.cons   -- etc.
        2
        (
          list.cons
            3
            list.nil
        )
    )

-- it seems to have worked 
#reduce three_list_nat''


-- notation, :: is infix for cons
-- [] notation adds nil at end
def three_list_nat''' := 1::2::3::list.nil
def three_list_nat'''' := [1,2,3]
def four_list_nat := 0::[1,2,3]       -- fun!


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

-- here with an implicit type parameter, making it equivalent to cons
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

-- okay, that looks good
-- but know that to which it desugars

example := prepend' nat 2 [3,4,5]
#eval prepend' nat 2 [3,4,5]

example := prepend 2 [3,4,5]
#eval prepend 2 [3,4,5]

#eval 2::[3,4,5]



-- a version of tail that "loops at zero" 
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

-- When applying it a proof about the first argument has to be given 
#eval head' [1,2,3] begin contradiction end   -- proof as a proof script
#eval head' [1,2,3] (by contradiction)        -- alternative syntax, fyi
#eval head' ([] : list nat) _                 -- you'll need a proof of list.nil ≠ list.nil!


-- implement the function, no need to (do not try) to match on α
-- it's named before the colon and is global to this definition
-- we do want to match (do case analysis) on l, so it's after :
-- def tail {α : Type} : ∀ (l : list α), (l ≠ list.nil) → list α 
-- |
-- |


-- let's implement a "safe" pred function using tactics
def pred' : ∀ (n : nat), (n ≠ nat.zero) → ℕ :=
begin
assume n,
cases n with n',
assume h,
contradiction,
assume h,
exact n',
end

#reduce pred' 5 _
#reduce pred' 2 _
#reduce pred' 0 _

-- here's the same predecessor function presented differently
def pred'' : ∀ (n : nat), (n ≠ nat.zero) → ℕ 
| nat.zero h := by contradiction
| (nat.succ n') h := n'
 
-- a different safe predecessor function using an option return 
def pred''' : nat → option nat  
| nat.zero := option.none
| (nat.succ n') := some n'

-- the same ideas work for safe head and tail functions on lists
universe u
def tail : ∀ {α : Type u} (l : list α), (l ≠ list.nil) → list α  
| α list.nil p := by contradiction
| α (h::t) p := t  

-- apply tail to [1,2,3] giving the proof as a tactic script
#eval tail [1,2,3] 
begin 
assume p,
contradiction,
end

-- cleaner this way
#eval tail [1,2,3] (by contradiction)
#eval tail [2,3] (by contradiction)
#eval tail [3] (by contradiction)
#eval @tail nat [] (by contradiction)      -- no can do!

-- let's try it with a tactic script
#eval @tail nat [] 
begin 
assume h,   -- we're stuck, and that's good!
end


-- append: the list analog of natural number addition
-- please do compare/contrast list.append and nat.add
def appnd {α : Type} : list α → list α → list α
| list.nil m := m
| (h::t) m := h::appnd t m 

#eval appnd [1,2,3] [4,3,2]

