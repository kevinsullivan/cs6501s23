import algebra.group


-- We represent the set of monoid elements (rotations) as a type
inductive rot_sym_eqtri 
| r0
| r120
| r240

open rot_sym_eqtri

-- We represent the operation as a binary operation on this
def rot_mul : rot_sym_eqtri → rot_sym_eqtri → rot_sym_eqtri 
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

theorem rot_left_ident : ∀ (r : rot_sym_eqtri), rot_mul r0 r = r  :=
begin
assume r,
cases r,
repeat {apply rfl},
end 

theorem rot_right_ident : ∀ (r : rot_sym_eqtri), rot_mul r  r0 = r :=
begin
assume r,
cases r,
repeat {apply rfl},
end 

-- And we need a proof that the operation is associative

theorem rot_mul_assoc : 
  ∀ (e1 e2 e3 : rot_sym_eqtri), 
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


instance : has_mul rot_sym_eqtri  := ⟨ rot_mul ⟩ 


instance : semigroup rot_sym_eqtri := ⟨ rot_mul, rot_mul_assoc ⟩ 

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

instance : has_one rot_sym_eqtri := ⟨ r0 ⟩ 
instance : mul_one_class rot_sym_eqtri := ⟨ r0, rot_mul, rot_left_ident, rot_right_ident ⟩ 




def rot_npow : ℕ → rot_sym_eqtri → rot_sym_eqtri 
| 0 x := r0
| (nat.succ n') x := rot_mul x (rot_npow n' x)

instance : monoid rot_sym_eqtri := 
⟨
  rot_mul,
  rot_mul_assoc,
  r0,
  rot_left_ident,
  rot_right_ident,
  rot_npow,
⟩ 



-- Notations!
#reduce (1 : rot_sym_eqtri)
#reduce (r120 * 1)
#reduce (r120 * r120)

-- foldr using monoid notation
def foldr {α : Type} [monoid α] : list α → α
|  list.nil := 1
| (h::t) := h * foldr t

#reduce foldr []
#reduce foldr [r120,r120]
#reduce foldr [r120,r120,r120]


