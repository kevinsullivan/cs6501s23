


universe u
def comp {α β γ : Type u} : (α → β) → (β → γ) → (α → γ)
| f g := λ a, g ( f a)

-- Standard notation reversing argument order: g after f

notation : g ` ∘ ` f := comp f g



-- apply comp explicitly in your answer
def ev_len : string → bool := _ 

-- do it again but using ∘ notation
def ev_len' := _

-- test cases
example : ev_len "Hello" = ff := rfl
example : ev_len' "Hello" = ff := rfl
example : ev_len "Hello!" = tt := rfl
example : ev_len' "Hello!" = tt := rfl







universe v    -- u is already a universe level 

def map {α : Type u} {β : Type v} : (α → β) → list α → list β 
| f list.nil  := list.nil
| f (h::t)    := (f h)::(map f t)

-- nat → nat
#eval map nat.succ [0,1,2,3,4]        
#eval map (λ n, n * n) [0,1,2,3,4]

-- string → nat
#eval map string.length ["Hello", "Lean", "We", "Love", "You!"]

#check @list.map






-- In this example we also introduce "match" for doing case analysis on a term
def filter' {α : Type u} : (α → bool) → list α → list α
| p list.nil := list.nil
| p (h::t) :=   
    match (p h) with 
      | tt := h::filter' p t
      | ff := filter' p t
    end

#eval filter' ((λ n, n % 2 = 0) ∘ (string.length)) ["Hello", "Lean", "We", "Love", "You!"]

-- same function using if/then/else; there's still a coercion happening from (p h) to bool 
def filter {α : Type u} : (α → bool) → list α → list α
| p list.nil := list.nil
| p (h::t) := if (p h) then (h::filter p t) else (filter p t)



-- Your answer here:



