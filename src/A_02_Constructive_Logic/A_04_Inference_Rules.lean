

#check true                   -- a proposition
example : true := true.intro  -- a proof of it




#check false
#check @false.elim  -- false.elim : Π {C : Sort u_1}, false → C

-- explicit application of Lean's false.elim rule
example : false → 0 = 1 := 
begin 
assume f, 
exact false.elim f,       -- So what is C (_)? It's the goal, 0 = 1.
-- exact @false.elim _ f,    -- Note that C is an implicit argument!
end

/- 
We can also do case analysis on f. We will get
one case for each possible form of proof, f. As
there are no proofs of f, there are no cases at
all, and the proof is completed. 
-/
example : false → 0 = 1 := 
begin 
assume f, 
cases f, 
end

/-
False eliminations works for "return types" in any
type universe. When the argument and return types 
are both in Prop, one has an ordinary implication.  
-/
example : false → nat :=
begin
assume f,
cases f,
-- contradiction,  -- this tactic works here, too
end


namespace hidden
structure and (A B : Prop) : Prop :=
intro :: (left : A) (right : B)
end hidden


example (b : bool) :  bnot (bnot b) = b :=
begin
cases b,              -- NB: one case per constructor
repeat { apply rfl }, -- prove goal *in each case*
-- QED.               -- thus proving it in *all* cases
end


-- Case analysis on *proof* values 
example (X Y: Prop) : X ∧ Y → X := 
begin
assume h,           -- a proof we can *use*
cases h with x y,   -- analyze each possible case
exact x,            -- also known as destructuring
end

-- We can even use "case analysis" programming notation!
example (X Y: Prop) : X ∧ Y → X
| (and.intro a b) := a




namespace hidden
inductive or (A B : Prop) : Prop
| inl (h : A) : or
| inr (h : B) : or
end hidden


-- Example using a lambda expression. Be sure you understand it. 
example (A B : Prop) : A → A ∨ B := fun (a : A), or.inl a
/-
Ok, you might have notice that I've been declaring some named
arguments to the left of the : rather than giving them names
with ∀ bindings to the right. Yes, that's a thing you can do. 
Also note that we *do* bind a name, *a*m to the assumed proof
of *A*, which we then use to build a proof of *A ∨ B*. That's
all there is to it.
-/


-- or.elim : ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-- deduce c from proofs of a ∨ b, a → c, and b → c, 
#check @or.elim 

example (P Q R : Prop) : P ∨ Q → (P → R) → (Q → R) → R
| (or.inl p) pr qr := pr p
| (or.inr q) pr qr := qr q



example : ∀ P Q, P ∨ Q → Q ∨ P :=
begin
assume P Q h,
cases h with p q,
exact or.inr p,
exact or.inl q,
end


example : ∀ P Q R, P ∨ (Q ∨ R) → (P ∨ Q) ∨ R :=
begin
assume P Q R h,
cases h with p qr,
left; left; assumption,
cases qr with q r,
left; exact or.inr q,
right; assumption,
end



-- ¬¬X ⊢ X                 -- negation elimination
-- X → ⊥ ⊢ ¬X             -- negation introduction


-- def not (a : Prop) := a → false
-- prefix `¬`:40 := not
#check not

example : ¬ 0 = 1 :=
begin
show 0 = 1 → false,
assume h,
contradiction,
end


example : 0 = 1 → false :=
begin
assume h,
cases h,
end 

example : ¬ 0 = 1 :=
begin
assume h,
cases h,
end 

example : 0 ≠ 1 :=
begin
assume h,
cases h,
end 


example : ∀ (X : Prop), ¬¬X → X :=
begin
assume X h,
-- can't do case analysis on a function
cases h,
-- we're stuck with nowhere left to go!
end



-- A proof of 0 = 0 by contradition 
example : 0 = 0 :=
begin
by_contradiction, -- applies ¬¬P → P
have eq0 := eq.refl 0,
contradiction,
end



#check @classical.em 

theorem foo : ∀ P, (P ∨ ¬ P) → (¬¬P → P) :=
begin
assume P,
assume em,
assume notNotP,
cases em,
-- case 1
assumption,
contradiction,
end

example : 0 = 0 :=
begin
by_contradiction,
have zez := eq.refl 0,
contradiction, 
end

theorem demorgan1 : ∀ P Q, ¬(P ∧ Q) ↔ (¬P ∨ ¬ Q) :=
begin
assume P Q,
--apply iff.intro _ _,
split,   

-- FORWARD
assume h,


have ponp := classical.em P,
have qonq := classical.em Q,

cases ponp with p np,
cases qonq with q nq,
have pandq := and.intro p q,
contradiction,

apply or.inr nq,
apply or.inl np,

-- BACKWARDS
assume h,
cases h,

assume pandq,
have p := and.elim_left pandq,
-- cases pandq with p q,
contradiction,

assume pandq,
cases pandq with p q,
contradiction,

end

example : ∀ (P : Prop), ¬ (P ∧ ¬P) :=
begin
assume P,
assume h,
cases h with p np,
apply false.elim (np p),
end

example : ∀ P Q R, P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) :=
begin
assume P Q R,
assume h,
apply and.intro _ _,

cases h with p qandr,
exact or.inl p,
cases qandr with q r,
apply or.inr q,
cases h,
exact or.inl h,
cases h,
exact (or.inr h_right)

end



-- 13. X → Y, Y → X ⊢ X ↔ Y   -- iff introduction
-- 14. X ↔ Y ⊢ X → Y          -- iff elimination left
-- 15. X ↔ Y ⊢ Y → X          -- iff elimination right


example (P Q : Prop) : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) :=
begin
split,

-- FORWARD
assume piffq,
cases piffq with pq qp,
exact and.intro pq qp,

-- BACKWARD
assume pqqp,
cases pqqp with pq qp,
exact iff.intro pq qp,
end  



