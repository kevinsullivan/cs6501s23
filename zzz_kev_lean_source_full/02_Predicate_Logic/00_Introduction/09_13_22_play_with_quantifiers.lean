/-
In this file, we present predicate logic formalizations
of the informal propositions on the last slide from today's
class. We repeat each one as a comment below, followed by 
a formal version in the constructive predicate logic of the
Lean Prover tool. 
-/

/-
Here we define some terms that we then use in the expressions below:
There is a type of object called Person. The variables P, Q, and R
refer to objects of this type. Meanwhile, isMortal and isHappy are
predicates, each taking one Person as an argument and "reducing" to 
a proposition (in Lean any proposition is an object of type Prop!).
Similarly, likes and might_like are predicates each taking *two*
arguments of type Person and reducing to a proposition about them.
Finally, isEven, isOdd, and isPrime are all predicates taking one
natural number argument and reducing to a proposition "about" that
number.
-/
variable Person : Type        -- Person is a type
variables P Q R : Person      -- P Q R are objects of this type
variables isMortal isHappy : Person → Prop   -- one-argument predicates, Person arg
variables likes might_like: Person → Person → Prop  -- predicates taking two Persons
variables isEven isOdd isPrime : nat → Prop -- one nat argument predicates


/-
With these terms defined, we can now write all our propositions
in a completely precise and fully type-checked syntax. You cannot
fool the Lean type checker. In the expressions below, #check is a
command to Lean asking it to typecheck and output the type of each
expression. These expressions are all propositions, so their types
are all "Prop," which is the type of all logical propositions that
you might write in Lean. If you hover over the #check command or
open the Lean InfoView window, you can see what Lean reports as the
types of these expressions.
-/

-- Every person is mortal
#check ∀ (P : Person), isMortal P

-- Someone is happy
#check ∃ (P : Person), isHappy P

--  Someone likes everyone
#check ∃ (P : Person), ∀ (Q : Person), likes P Q

-- Everyone likes someone
#check ∀ (P : Person), ∃ (Q : Person), likes P Q

-- There is someone everyone likes
#check ∃ (P : Person), ∀ (Q : Person), likes Q P

-- For any persons, P, Q, R, if P likes Q, and Q likes R, then P might like R
#check ∀ (P Q R : Person), likes P Q → likes Q R → might_like P R

-- The enemy of your enemy is your friend
#check ∀ P Q R, ¬ likes P Q → ¬ likes Q R → likes P R   -- Look ma, no type annotations

-- For any natural number, n, if n is even then n+1 is odd
#check ∀ (n : nat), isEven n → isOdd (n + 1)

-- With n being any natural number, if n >= 2, then if no number in 2,...,n/2 
-- divides n evenly, then n is prime
#check ∀ (n : nat), n >= 2 → (∀ m, m >=2 ∧ m <= n/2 → n%m ≠ 0) → isPrime n
-- exercise: rewrite that using an ∃ instead of ∀ in the parentheses

-- No one likes everyone
#check ¬∃ (P : Person), ∀ (Q : Person), likes P Q

-- If there’s a person everyone likes, then everyone likes someone
#check (∃ (P : Person), ∀ (Q : Person), likes Q P) → (∀ P, ∃ Q , likes P Q)