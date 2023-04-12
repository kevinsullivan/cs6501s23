import algebra.group


-- We represent the set of monoid elements (rotations) as a type
inductive rot 
| r0
| r120
| r240

open rot

-- We represent the operation as a binary operation on this
def rot_mul : rot → rot → rot 
| r0 r0 := r0
| r0 r120 := r120
| r0 r240 := r240
| r120 r0 := r120
| r120 r120 := r240
| r120 r240 := r0
| r240 r0 := r240
| r240 r120 := r0
| r240 r240 := r120

-- We need a proof that r0 is an identity for this operation

theorem rot_left_ident : ∀ (r : rot), rot_mul r0 r = r  :=
begin
assume r,
cases r,
repeat {exact rfl,}
end 

theorem rot_right_ident : ∀ (r : rot), rot_mul r  r0 = r :=
begin
assume r,
cases r,
repeat {apply rfl},
end 

-- And we need a proof that the operation is associative

theorem rot_mul_assoc : 
  ∀ (e1 e2 e3 : rot), 
    rot_mul (rot_mul e1 e2) e3 = rot_mul e1 (rot_mul e2 e3) :=
begin
assume e1 e2 e3,

cases e1,
repeat { 
  cases e2,
  repeat { 
    cases e3,
    repeat {exact rfl}},  
  },
end 



#check @monoid
/-
class monoid (M : Type u) extends semigroup M, mul_one_class M :=
(npow : ℕ → M → M := npow_rec)
(npow_zero' : ∀ x, npow 0 x = 1 . try_refl_tac)
(npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x . try_refl_tac)
-/


#check @semigroup
/-
class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
-/


#check @has_mul
/-
class has_mul      (α : Type u) := (mul : α → α → α)
-/


-- see instance constructor type
#check has_mul.mk 

-- construct instance using anonymous constructor notation
instance : has_mul rot  := ⟨ rot_mul ⟩ 


-- check the constructor to see the required field values 
#check @semigroup.mk 
/-
Π {G : Type u}                                -- carrier set implicit
  (mul : G → G → G),                          -- operator
  (∀ (a b c : G), a * b * c = a * (b * c)) →  -- proof of associativity 
semigroup G
-/

instance : semigroup rot := ⟨ rot_mul, rot_mul_assoc ⟩ 
#check @mul_one_class



#check @mul_one_class
#check @has_one
#check @has_mul 

/-
class mul_one_class (M : Type u) extends has_one M, has_mul M :=
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)

class has_one      (α : Type u) := (one : α)
-/
instance : has_one rot := ⟨ r0 ⟩ 

#check @mul_one_class.mk 
/-
 Π {M : Type u} 
   (one : M) 
   (mul : M → M → M), 
   (∀ (a : M), 1 * a = a) → 
   (∀ (a : M), a * 1 = a) → 
  mul_one_class M
-/
instance : mul_one_class rot := 
⟨ r0, rot_mul, rot_left_ident, rot_right_ident ⟩ 

-- Finally we'll need a definition of npow
def rot_npow : ℕ → rot → rot 
| 0 x := 1
| (nat.succ n') x := rot_mul x (rot_npow n' x)


#check @monoid.mk 
/-
Π {M : Type u_1} 
  (mul : M → M → M),
  (∀ (a b c : M), a * b * c = a * (b * c)) →
  Π (one : M) 
    (one_mul : ∀ (a : M), 1 * a = a) 
    (mul_one : ∀ (a : M), a * 1 = a)
    (npow : ℕ → M → M),
    -- synthesized parameters
    auto_param (∀ (x : M), npow 0 x = 1) (name.mk_string "try_refl_tac" name.anonymous) →
    auto_param (∀ (n : ℕ) (x : M), npow n.succ x = x * npow n x) (name.mk_string "try_refl_tac" name.anonymous) →
  monoid
-/
instance : monoid rot := 
⟨
  rot_mul,
  rot_mul_assoc,
  1,
  rot_left_ident,
  rot_right_ident,
  rot_npow,
⟩ 

-- Synthesized fields
#check monoid.npow_zero'
#reduce monoid.npow_succ'



-- Notations!
#reduce (1 : rot)
#reduce (r120 * 1)
#reduce (r120 * r120)

-- foldr using monoid notation
def mul_foldr {α : Type} [monoid α] : list α → α
|  list.nil := 1
| (h::t) := h * mul_foldr t

#reduce mul_foldr []
#reduce mul_foldr [r120,r120]
#reduce mul_foldr [r120,r120,r120]

-- we could also do this, as in the previous chapter
def rot_comp_n := @mul_foldr rot
#reduce rot_comp_n []
#reduce rot_comp_n [r120,r120]
#reduce rot_comp_n [r120,r120,r120]


