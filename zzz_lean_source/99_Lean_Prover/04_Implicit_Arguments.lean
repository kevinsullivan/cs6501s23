/-
If a function, f, takes a type, T, as its first 
argument, and a value, t, of that very type, T, as 
its second argument, then when you fully apply the
function (to all its arguments), you will have to 
give two arguments: a value for T, in other words
a type; and a value, t, of that type.  

But why should you have to write out "nat" when Lean
knows from 4 that nat is all it can be? Good news: if
you specify the argument as implicit, then it will be
inferred, and if Lean can't infer it it will tell you.
-/


-- identity function on natural numbers
def id_nat : ℕ → ℕ 
| n := n

example : id_nat 5 = 5 := rfl

def id_string : string → string 
| s := s

def id_bool : bool → bool 
| b := b

-- def id_T (T : Type) (a : T)
def id_T' (T : Type) : T → T
| t := t

def id_T'' : ∀ (T : Type), T → T
| T t := t

#eval id_T' nat 3
#eval id_T' bool tt
#eval id_T' string "I love logic"

#eval id_T'' nat 3
#eval id_T'' bool tt
#eval id_T'' string "I love logic"

def id_T {T : Type} : T → T
| t := t

#eval id_T 3
#eval id_T tt
#eval id_T "This is so cool"


#eval @id_T nat 3

#check id_T
#check @id_T





def identity1 : ∀ (T : Type) (t : T), T := 
begin
assume T t,
exact t,
end 

#eval identity1 nat 1 
#eval identity1 string "Hi!"

  /-
 This pair of examples is really very cool, as 
 it illustrates what in computer science we call
 parametric polymorphism. That means that you 
 specify a type as a parameter and then values
 of the given types as additional arguments,
and what this gives you is a whole family of
functions, here one for each type you might pass
as the actual value of the first parameter. 
And, here's the real key idea: the "code" is the
same no matter the value of the type parameter. 
Parametric polymorphism.

Try it out. Use #eval

as nat, bool, string, 0 = 0, etc) you might 
pass as the first argument, the "type " 
  -/

/-=
  arguments that are to 
be inferred from context rather than specified explicitly. When
you #check a type, it prints implicit arguments as numbered
"meta-variables." To make Lean print the type making all of
the arguments explicit, you can use @.
-/


def example1A { T : Type } (t : T) := t
def example1B { T : Type } (t : T) : T := t

/-
When we specify arguments of a function or predicate, we can
declare them as named arguments (just in in Java or Python)m
before the colon. We can then continue the argument list after
the colon using arrown notation. 
function 
-/
