



variable Person : Type        -- Person is a type
variables P Q R : Person      -- P Q R are objects of this type
variables isMortal isHappy : Person → Prop   -- one-argument predicates, Person arg
variables likes might_like: Person → Person → Prop  -- predicates taking two Persons
variables isEven isOdd isPrime : nat → Prop -- one nat argument predicates


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
