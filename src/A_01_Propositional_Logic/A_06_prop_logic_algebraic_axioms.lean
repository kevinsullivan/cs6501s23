import .A_05_prop_logic_properties
namespace cs6501




example : 
∀ (p q : prop_expr) (i : prop_var → bool),
  pEval (p ∧ q) i = pEval (q ∧ p) i :=
and_commutes  -- proof from last chapter






notation (name := pEval) ` ⟦ ` p ` ⟧ `  :=  pEval p


-- start a section
section prop_logic_axioms

-- Let p, q, r, and i be arbitrary expressions and an 
-- interpretation
variables (p q r : prop_expr) (i : prop_var → bool)



def and_commutes' := (⟦(p ∧ q)⟧ i) = (⟦(q ∧ p)⟧ i) 
def or_commutes' :=  ⟦(p ∧ q)⟧ i = ⟦(q ∧ p)⟧ i



#reduce and_commutes' p q i


-- by unfolding definitions and case analysis 
example : and_commutes' p q i := 
begin
unfold and_commutes' pEval bin_op_sem,
cases ⟦ p ⟧ i,
repeat { cases ⟦ q ⟧ i; repeat { apply rfl } },
end 


def and_associative_axiom :=  ⟦(p ∧ q) ∧ r⟧ i = ⟦(p ∧ (q ∧ r))⟧ i
def or_associative_axiom :=   ⟦(p ∨ q) ∨ r⟧ i = ⟦(p ∨ (q ∨ r))⟧ i


def or_dist_and_axiom := ⟦p ∨ (q ∧ r)⟧ i = ⟦(p ∨ q) ∧ (p ∨ r)⟧ i
def and_dist_or_axiom := ⟦p ∧ (q ∨ r)⟧ i = ⟦(p ∧ q) ∨ (p ∧ r)⟧ i


def demorgan_not_over_and_axiom := ⟦¬(p ∧ q)⟧ i = ⟦¬p ∨ ¬q⟧ i
def demorgan_not_over_or_axiom :=  ⟦¬(p ∨ q)⟧ i = ⟦¬p ∧ ¬q⟧ i


def negation_elimination_axiom := ⟦¬¬p⟧ i = ⟦p⟧ i



def excluded_middle_axiom := ⟦p ∨ ¬p⟧ i = ⟦⊤⟧ i   -- or just tt




def no_contradiction_axiom := ⟦p ∧ ¬p⟧ i = ⟦⊥⟧ i   -- or just tt



def implication_axiom := ⟦(p => q)⟧ i = ⟦¬p ∨ q⟧ i  -- notation issue

example : implication_axiom p q i := 
begin
unfold implication_axiom pEval bin_op_sem un_op_sem,
cases ⟦ p ⟧ i; repeat { cases ⟦ q ⟧ i; repeat { apply rfl } },
end



end prop_logic_axioms
end cs6501

