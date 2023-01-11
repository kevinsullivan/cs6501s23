/- Review: Sets as defined by membership predicates

Review: We specific a set of objects of some 
type, α, as a predicate, p : α → Prop. Recall
that p takes an argument, a, of type α, and 
reduces to a proposition, p_a, about a. If a
"satisfies" p, then it has the property that
p specifies, and otherwise not. 

For example, if α is ℕ, and even : ℕ → Prop
:= λ n, n % 2 = 0, then even n will be true
(have a proof) for any even actual parameter,
n, otherwise false.  The predicate represents
the set precisely and completely.
-/

-- Logical notation, logical thinking, even is a predicate
def isEven : ℕ → Prop := fun n, n % 2 = 0   -- λ expression

-- Set notation, set thinking, even as a set (a collection of objects)
def evens := { n | isEven n } -- evens is the set of n that satisfy even

-- Logical notation, predicate applications yielding propositions
example : evens 0 := rfl
example : evens 1 := rfl
example : evens 2 := rfl

-- Set mmber notation for the same predicate applications
example : 0 ∈ evens := rfl
example : 1 ∈ evens := rfl
example : 2 ∈ evens := rfl

/-
So these expressions all mean the same thing:
3 ∈ evens   -- set membership notation
evens 3     -- predicate application notation
3 % 2 = 0   -- predicate application reduced to a propostion
-/

/-
Takeaway: To formally specify a set, all you
have to do is specify the membership predicate.
Then you can use that predicate to express your
sets using set builder notation. Step 1: specify
the predicate. Step 2: use it within set builder
expressions. Here's a by now familiar example.
-/

/-
Exercise: use set membership notation to write the next
few test cases after the ones given above: for argument
values of 3, 4, and 5. It's not challenging. But now take
the opportunity to think though how these tests are working. 
And marvel at what our proof assistant: guaranteeing to find 
and finding mismatches between proofs and the propositions 
they are claimed to prove. 
-/

/-
Exercise: formally specify the set of odd natural numbers
breaking up your specification into the two parts discussed
above. That is, define isOdd, the predicate, and then odds, 
the set, separately. Then state and prove the propositions, 
2 ∉ odds, and 3 ∈ odds. (Use example.)
-/