

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


/-
-- formalize the rest
-- 9. ¬¬X ⊢ X                 -- negation elimination
-- 10. X → ⊥ ⊢ ¬X             -- negation introduction
-- 11. (X ⊢ Y) ⊢ (X → Y)      -- a little complicated
-- 12. X → Y, X ⊢ Y           -- arrow elimination
-- 13. X → Y, Y → X ⊢ X ↔ Y    -- iff introduction
-- 14. X ↔ Y ⊢ X → Y          -- iff elimination left
-- 15. X ↔ Y ⊢ Y → X          -- iff elimination right
-/