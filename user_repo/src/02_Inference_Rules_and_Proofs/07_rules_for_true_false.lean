
section pred_logic
variables X Y Z : Prop



#check true
#check false
#check ∀ (P : Prop), P ∨ true



theorem true_is_true : true := true.intro





theorem a_proof_of_false : false := _   -- no can do!



def p1 : Prop := false → false
def p2 : Prop := false → true
def p3 : Prop := true → true
def p4 : Prop := true → false
def p5 : Prop := false → 2 = 3
def p6 : Prop := false → 0 = 0
def p7 : Prop := ∀ (P : Prop), true → P
def p8 : Prop := ∀ (P : Prop), false → P 

-- TEXT:
Let's look at the case of p8. Prove that it's true.
-- TEXT.

theorem p8_is_true : p8 := 
begin
unfold p8,
assume P,
assume f,
apply false.elim f,
end 


-- def p1 : Prop := false → false
theorem x : p1 := 
begin
  unfold p1,
  assume f : false,
  exact f,
end

-- false → true
example : p2 := 
begin
  unfold p2,
  assume f,           -- move premise into context
  --exact true.intro,   -- don't have to use assumption
  -- apply false.elim f,
  contradiction,
end

example : p3 := 
begin
unfold p3,
assume t,
exact t,    -- exact true.intro also works
end

example : p4 := 
begin
unfold p4,
assume t,
end

example : p5 := 
begin
unfold p5,
assume f,
cases f,
end

example : p6 := 
begin
unfold p6,
assume f,
cases f,
-- exact rfl,
end


example : p7 := 
begin
unfold p7,
intro P,
assume t,
-- stuck
end

example : p8 := 
begin
unfold p8,
assume P f,
cases f,
end
