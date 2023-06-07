-- import .A_05_recursive_proofs

import algebra.group
namespace cs6501


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



