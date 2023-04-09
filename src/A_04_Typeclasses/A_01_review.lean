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


end cs6501
