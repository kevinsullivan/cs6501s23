


namespace impl_cstyle

def sub1 (n : ℕ) : ℕ :=   -- first arg named to left of :
  match n with            -- match does case analysis after all
  | 0 := 0
  | (n' + 1) := n'
  end

def add2 (n : ℕ) := n+2   -- n+2 is short for succ(succ n)!


example : sub1 0 = 0 := rfl
example : sub1 1 = 0 := rfl
example : sub1 2 = 1 := rfl
example : sub1 3 = 1 := rfl  -- bad test
example : add2 0 = 2 := rfl
example : add2 1 = 3 := rfl
example : add2 2 = 4 := rfl
example : add2 3 = 6 := rfl -- bad test

end impl_cstyle



def my_bool_and : bool → bool → bool 
| tt tt := tt
| tt ff := ff
| ff tt := ff
| ff ff := ff




def my_bool_and2 : bool → bool → bool 
| tt tt := tt
| _ _ := ff




example : 
  ∀ (b1 b2 : bool), 
    my_bool_and b1 b2 = 
    my_bool_and2 b1 b2 
  :=
begin
assume b1 b2, -- bind argument names

-- case analysis on b1 
cases b1,     

-- b1 false

-- case analysis on b2
cases b2,
-- b2 false 
apply rfl,
-- b2 true
apply rfl,

-- b1 true

-- case analysis on b2
cases b2,
-- b2 false
apply rfl,
-- b2 true
apply rfl,
end 



example : my_bool_and tt tt = tt := rfl
example : my_bool_and tt ff = ff := rfl
example : my_bool_and ff tt = ff := rfl
example : my_bool_and ff ff = ff := rfl

