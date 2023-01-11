/-
Suppose a function, f, takes an arbitrary string, s, 
as an argument, and returns a natural number result.

We can write the type of f as string -> nat, or formally, 
(f : string -> nat).

In Lean and languages like it, we write the application of f to s as "f s". In Python we'd write it as f(s).

So we can apply (f : string -> nat) to a value (s : string) and the result is a natural number (nat).

Arrow elimination is function application!

That's how it works in the world of computation. Now let's turn to logic.

Instead of the data types, string and nat, suppose P and Q are arbitrary propositions.

That means that P -> Q is also a propositions, "If P then Q". 

Now suppose that you've proven P -> Q and that pq is a proof of it.

Just like we had (f : string -> nat) above, now we have (pq : P -> Q).

You  can even think of pq as a function: one that takes a proof of P and returns a proof of Q!

That means that whenever P is true (with a proof, p), then (pq p) is a proof of Q.

In other words, because you have (pq: P -> Q) and (p : P) then (pq q)  is a proof of Q.

If P -> Q is true and P is true then Q must be.

If you have a proof of P -> Q and you have a proof of P you can construct a proof of Q.

That's arrow elimination.

Does this help?

-/