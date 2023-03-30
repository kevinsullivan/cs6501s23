-- import .A_05_recursive_proofs

import algebra.group
namespace cs6501


structure monoid' (α : Type) : Type := mk::
  -- data values
  (op : α  → α  → α )   -- data
  (e : α )              -- data
  -- statements and proofs of laws
  (ident : ∀ a, op e a = a ∧ op a e = a)
  (assoc: ∀ a b c, op a (op b c) = op (op a b) c)


-- QUOTE
-- monoid instances

def nat_add_monoid' := monoid'.mk nat.add 0 sorry sorry -- zero_ident_add_nat nat_add_assoc  
def nat_mul_monoid' := monoid'.mk nat.mul 1 sorry sorry -- mul_one_ident_nat nat_mul_assoc 
def monoid_list_append' {α : Type} : @monoid' (list α) := monoid'.mk list.append [] sorry sorry 



def foldr' (α : Type) (m : monoid' α) : list α → α  
| list.nil := match m with (monoid'.mk op e _ _) := e end
| (h::t) := match m with (monoid'.mk op e _ _) := m.op h (foldr' t) end


-- Safe use of monoid instances folds
#reduce foldr' nat nat_add_monoid' [1,2,3,4,5]
#reduce foldr' nat nat_mul_monoid' [1,2,3,4,5]
#reduce foldr' (list nat) monoid_list_append' [[1,2,3],[4,5,6],[7,8,9]]

-- Defining n-ary operators(partial evaluation)
def nat_add_n := foldr' nat nat_add_monoid'
def nat_mul_n := foldr' nat nat_mul_monoid'
def list_app_n {α : Type} := foldr' (list α)  (@monoid_list_append' α)  -- study this

-- Applying n-ary versions of binary operators to *lists* of argument values
#eval nat_add_n [1,2,3,4,5,6,7,8,9,10]
#eval nat_mul_n [1,2,3,4,5,6,7,8,9,10]
#eval list_app_n [[1,2,3],[4,5,6],[7,8,9]]
#eval list_app_n [ ["Hello", ", ", "Logic!"], ["You", " ", "are", " ", "Cool!"]]



structure mul_monoid' (α : Type) : Type := mk::
  (op : α  → α  → α )   -- data
  (e : α )              -- data
  (ident : ∀ a, op e a = a ∧ op a e = a)
  (assoc: ∀ a b c, op a (op b c) = op (op a b) c)

-- unfortunate but unavoidable duplication 
structure add_monoid' (α : Type) : Type := mk::
  (op : α  → α  → α )   -- data
  (e : α )              -- data
  (ident : ∀ a, op e a = a ∧ op a e = a)
  (assoc: ∀ a b c, op a (op b c) = op (op a b) c)

def  mul_foldr' {α : Type} (m : mul_monoid' α) : list α → α 
| list.nil := match m with (mul_monoid'.mk op e _ _) := e end
| (h::t) := match m with (mul_monoid'.mk op e _ _) := m.op h (mul_foldr' t) end

def  add_foldr' {α : Type} (m : add_monoid' α) : list α → α 
| list.nil := match m with (add_monoid'.mk op e _ _) := e end
| (h::t) := match m with (add_monoid'.mk op e _ _) := m.op h (add_foldr' t) end

-- Question: what are the types of mul_ and add_monoid'?
#check @add_monoid'
#check @mul_monoid'



@[class] structure mul_monoid (α : Type) : Type := mk::
  (op : α  → α  → α )   -- data
  (e : α )              -- data
  (ident : ∀ a, op e a = a ∧ op a e = a)
  (assoc: ∀ a b c, op a (op b c) = op (op a b) c)

-- unfortunate but unavoidable duplication 
class add_monoid (α : Type) : Type := mk::
  (op : α  → α  → α )   -- data
  (e : α )              -- data
  (ident : ∀ a, op e a = a ∧ op a e = a)
  (assoc: ∀ a b c, op a (op b c) = op (op a b) c)


@[instance] def nat_add_monoid : add_monoid nat := add_monoid.mk nat.add 0 sorry sorry -- zero_ident_add_nat nat_add_assoc  
instance list_append_monoid {α : Type} : @add_monoid (list α) := add_monoid.mk list.append [] sorry sorry 


def  mul_foldr {α : Type} [m : mul_monoid α] : list α → α 
| list.nil := match m with (mul_monoid.mk op e _ _) := e end
| (h::t) := match m with (mul_monoid.mk op e _ _) := m.op h (mul_foldr t) end

def  add_foldr {α : Type} [m : add_monoid α] : list α → α 
| list.nil := match m with (add_monoid.mk op e _ _) := e end
| (h::t) := match m with (add_monoid.mk op e _ _) := m.op h (add_foldr t) end



#eval add_foldr [1,2,3,4,5]                 -- op = nat.add
#eval add_foldr [[1,2,3],[4,5,6],[7,8,9]]   -- op = list.append
#eval mul_foldr [1,2,3,4,5]                 -- error: no instance available!





instance nat_mul_monoid := 
  mul_monoid.mk nat.mul 1 sorry sorry           
instance bool_mul_monoid : mul_monoid bool := 
  mul_monoid.mk band tt sorry sorry 

#check mul_monoid
#check add_monoid
#eval mul_foldr [tt,ff,tt]
#eval add_foldr [tt,ff,tt]                      -- error: no instance


-- Exercise: define a typeclass instance to fix this error.


class default_value (α : Type) := mk::
(val : α)

instance nat_def : default_value nat := default_value.mk 0
instance bool_def : default_value bool := default_value.mk tt
instance list_def {α : Type} : default_value (list α) := default_value.mk []

def list_head {α : Type} [d : default_value α] : list α → α
| [] := d.val
| (h::t) := h

#eval list_head [1,2,3]                     -- returns nat
#eval list_head [ff,tt,ff]                  -- returns bool
#eval list_head [[1,2,3],[4,5,6],[7,8,9]]   -- returns list nat

#eval list_head ([] : list nat)             -- returns default nat!     
#eval list_head ([] : list bool)            -- returns default bool!
#eval list_head ([] : list string)          -- error: no default for string

-- EXERCISE: define a default_value typeclass instance to fix that error


-- First the typeclass
class has_mult (α : Type) :=    -- has_mul in Lean; also "dropping mk::"
(op : α → α → α)

-- Then an overloaded operator; applies right version of op for α 
def mult {α : Type} [has_mult α] (a b : α) := has_mult.op a b

instance has_mult_nat : has_mult nat := has_mult.mk nat.mul
instance has_mult_bool : has_mult bool := has_mult.mk band

#eval mult 3 4
#eval mult tt tt
#eval mult ff tt
#eval mult tt ff
#eval mult ff ff

-- Now all we need is a notation

notation (name := mult) a ` * ` b := mult a b

#eval tt * ff     -- this works well
#eval 2 * 3       -- oops, * already overloaded, thus *ambiguous*




#check monoid         -- extends semigroup, mul_one_class
#check semigroup      -- extends has_mul
#check has_mul        -- as we've seen
#check mul_one_class  -- extends has_one 
#check has_one        -- arbitrary value called "one"

-- See documentation for how it all fits together. 


end cs6501
