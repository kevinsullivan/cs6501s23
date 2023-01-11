/-*** def ***-/

/-
The def keyword in Lean establishes a new definition: a binding
of a variable to a value of a specified type. First, let's look
at binding names to values of a few data types.
-/

def five : ℕ := 5

/-
This definition declares five to be a variable name, to be bound
to a value of type ℕ, and in particular now bound to the value, 5.
We can now use #check to see that we've got what we expect here.
-/

#check five

/-
#check tells us that five is a correct expression and that it is
an expression of type ℕ.
-/

/-
Note that when Lean can infer the type of a variable from the 
value bound to it, you can elide the explicit "type judgment"
-/

def six := 6      -- type inference
#check 6
#check six



/-
Ok, now let's look at the case where we're working now with 
data values but with proofs of propositions. We'll start with
the proposition, true.
-/

def proof_of_true : true := true.intro

/-
Here we define proof_of_true to be a variable, meant to be 
bound to a "proof" (or proof value, or proof object) because 
"true" is a proposition not a data type. We then bind it to 
the proof value, true.intro, which, as you will recall, is the 
one and only proof of true in our logic. Proofs are mathematical
objects/values, just like data values.
-/

/-
It's worthwhile at this point to think hard again about types.
The type of proof_of_true in our logic is *true*. That's what
the "type judgement", (proof_of_true : true), expresses. And
of course the type of true is Prop.
-/

/-
When assigning proof values to variables, it's often beneficial
to work out the proof value a bit at a time. That's what proof
"scripts" are for. We could have written the previous example 
using a proof script just as well. 
-/

def proof_of_true2        : true := true.intro
def another_proof_of_true : true := begin exact true.intro end

/-
The script, :begin exact true.intro end", results in exactly the
proof value, true.intro, which is then bound to the variable, 
another_proof_of_true.
-/

#check proof_of_true
#check another_proof_of_true
#check true


/-
There's a deep parallel in our higher-order logic between data 
values and proof values, and between data types and propositions. 
Let's make this clear by examples.

- The type of "five" is ℕ, and the type of ℕ is Type
- The type of "Hi" is string, and the type of string is Type
- The type of tt is bool (in Lean), and the type of bool is Type.

- The type of true.intro is true, and the type of true is Prop 
- The type of proof_of_true is true, and the type of true is Prop
- The type of another_proof_of_true is true, and its type is Prop
-/

/-
Here's another example
-/

def a_fact : ∀ (P Q : Prop), P ∧ Q → P :=
begin
  assume P Q h,
  exact (and.elim_left h),
end 

def a_fact' : ∀ (P Q : Prop), P ∧ Q → P :=
  λ P Q h, and.elim_left h


/-
Here we declare a_fact to be a variable that is meant to be bound
(to have as its value) of proof of ∀ (P Q : Prop), P ∧ Q → P. The
proof script produces such a "proof" value, which is then bound to
the variable a_fact. The #check command reports that the "type" of
a_fact is ∀ (P Q : Prop), P ∧ Q → P. Propositions are types in our
higher-order logic, and just as Lean type checks the values you try
to bind to variables, giving errors if the types don't match, so in
the same way Lean checks the types of proof values to be sure they
match the propositions they're intended to be proofs of!
-/

def oops : ℕ := "Hi"       -- type error (read the error message)
def argh : ∀ (P Q : Prop), P ∧ Q → P := true.intro -- type error!

/-
Please read the error messages: in both cases we have a type error.
In the first example, we try to bind a string value, "Hi,"  to a 
variable declared to be of type ℕ, and that produces a type error. 
Similarly, when we try to bind a proof value, true.intro (a proof 
of true) to the variable, argh, we get a type error, because argh
is meant to be bound to a proof of ∀ (P Q : Prop), P ∧ Q → P.
-/

/-
We can clearly distinguish the use of the #check command to check 
the syntax and type of an expression you provide, from the use of
*type checking* in Lean (as in Java), which checks whether the type
of a value being bound to a variable is the same as the type that
the variable expects.
-/

/-
Whereas "def" binds a variable to a value in the "global
environment", the let keyword supports binding of values
to local variables, followed by evaluation of an expression
that uses that local variable.
-/

def x := 1
#eval x

#eval let a := 1 in a   --evaluates to 1

#check a                -- not defined in global environment


-- You can "nest" let expressions
#reduce  let a := 3 in 
          let b := 4 in
            let c := 5 in
              a*a + b*b = c*c


-- Within tactic scripts you leave off the "in" part
theorem pythag_25 : 3*3 + 4*4 = 5*5 :=
begin
  let a := 3,   
  let b := 4,
  let c := 5,
  show a * a + b * b = c * c,
  exact rfl,
end
