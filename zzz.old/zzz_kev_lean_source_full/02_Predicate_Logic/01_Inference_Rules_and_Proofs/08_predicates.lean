/- OVERVIEW

To readily understand the introduction rule and the
elimination rule for proofs of existential propositions
(starting with ∃), we first need a review of predicates.
Predicate in turn are thought of as functions from the
arguments to propositions "about" those arguments. So 
we also discuss function definitions, more generally,
and how we can specify them in various ways in Lean.
Finally we come back to the inference rules for ∃.
-/


/- PREDICATES

A predicate is a proposition with one or more parameters.
A proposition is a predicate with no remaining parameters!

You can think of a predicate it as a function that takes
one or more arguments and that reduces to a proposition
*about those particular values*. 

Here, for example, we define a predicate, called isEven,
that takes a natural number, n, as an argument and that
reduces to ("returns") the proposition, n % 2 = 0, *for
that particular n*.
-/

def isEven : ℕ → Prop :=
begin
assume n,
exact (n%2 = 0)
end 

/-
In fact, in Lean and similar logical programming systems,
a predicate *is* a function, and can thus be applied to an
argument of the specified type.
-/

#reduce isEven 0      -- 0 = 0
#reduce isEven 1      -- 1 = 0
#reduce isEven 2      -- 0 = 0
#reduce isEven 3      -- 1 = 0

/-
Note that the n%2 expression is evaluated automatically.
-/

/-
We will say that one or more values "satisfy" a predicate
when the corresponding proposition is true. In constructive
logic, that means when there's a proof of that proposition.
-/

example : isEven 0 :=
begin
simp [isEven],  -- new tactic: simplify by def'n of isEven
exact rfl,      -- forces reduction, tests equality
-- Yay! 0 is even
end


-- The rfl tactic does some simplification automatically
example : isEven 0 :=
begin
exact rfl,      -- forces reduction, tests equality
-- Yay! 0 is even
end

example : isEven 1 :=
begin
exact rfl,      -- there's no proof of 1=0
-- Ooooh noooo, 1 is not even
end

-- In fact we can prove the negation
example : ¬isEven 1 :=
begin
assume h,
simp [isEven] at h, -- more tactic fun (optional)
cases h,            -- no proofs of h so done
-- Yay! 1 is *not* even (proof by negation)
end

-- Proof that 2 is even
example : isEven 2 :=
begin
exact rfl,
-- Yay! 2 is even.
end

/-
A predicate expresses a *property* of the objects
it takes as arguments. Here the predicate expresses
the property of a natural number *being even* (or not).
Every natural number, n, that satisfies the predicate
(for which there's a proof) has the property expressed
by isEven,  while every number lacks this property.

We speak of values that "satisfy" a predicate as 
having the property that it expresses. Again, as an
example, evenness is a property of natural numbers.
Some have it, some don't. Every n for which n%2=0
has it, and no other number does (in ℕ).

A predicate can also be understood as specifying a 
*set* of values: in this example, the set of all 
even natural numbers: all those n where n % 2 = 0.
-/
