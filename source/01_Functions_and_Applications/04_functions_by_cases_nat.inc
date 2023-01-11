**********************************
Function definition by cases (nat)
**********************************
In the field of natural number arithmetic, one
of the fundamental functions is called successor.
In Lean it's nat.succ in Lean. It's the function
that, when applied to any nat, returns its successor,
the next larger nat. For example, the application
expression, (nat.succ 0), means 1, while the term,
nat.succ(nat.succ 0) means 2. (There are some
subtleties that we'll open up later.)

.. code-block:: lean

  example : nat.succ 0 = 1 := rfl

Question: What is the type of nat.succ? Figure it
out first, then you may check your answer by using 
#check.
syntax options for defining your own functions
==============================================
First we'll see how to implement basic Boolean functions,
such as "and." For a value of this type, there are just two
cases: tt and ff (in Lean). Then we'll turn to functions 
involving natural numbers, where for any natural number,
there are still just two cases but they are now n = 0 and
n > 0.
We will also use this discussion to present a few different
styles you can use to define functions in Lean. We wil in
particular implement two simple functions using each of three
different syntactic approaches. The functions, sub1, and add2,
respectively, return the predecessor, and the successor of the
successor of their arguments.

- sub1 : ℕ → ℕ 
    Given n, 
      case analysis:
        when n is 0, return 0,              -- case n = 0
        when n is (nat.succ n'), return n'  -- case n > 0 
- add2 : ℕ → ℕ 
    Given n, 
    return nat.succ(nat.succ n))

First, we'll see how we can define these
functions by declaring their types and then
using *tactic scripts* to produce correct 
implementations: values of these function
types that compute and return the correct
results. It feels like you're just proving
a theorem, but now the proof is a program!
that implements your task.

.. code-block:: lean

  namespace impl_script

To start, we'll declare each function just 
as we'd state a logical proposition, then
we'll "prove" they type by providing not
any program of this type but one that also
does what we require. Here we go.

.. code-block:: lean

  def sub1 : ℕ → ℕ :=
    begin
    -- give argument a name
    assume n,       
    -- do case analysis on n (=0, >0)
    cases n with n',
    -- case where n = 0
    exact 0,
    -- case where n = (succ n') > 0
    exact n',
    end
  
  
  def add2 : ℕ → ℕ :=
    begin
      assume n,   -- bind name to argument
      exact n+2,  -- means exactly nat.succ(nat.succ n)
    end

Next we can show that we can apply these
functions and that they work as expected.

.. code-block:: lean

  example : sub1 0 = 0 := rfl
  example : sub1 1 = 0 := rfl
  example : sub1 2 = 1 := rfl
  example : sub1 3 = 1 := rfl  -- bad test
  example : add2 0 = 2 := rfl
  example : add2 1 = 3 := rfl
  example : add2 2 = 4 := rfl
  example : add2 3 = 6 := rfl -- bad test

Case analysis by pattern matching (unification)
===============================================
Next we'll implement the same functions using
Lean's "pattern matching" or "by cases" syntax.

.. code-block:: lean

  def sub1 : ℕ → ℕ 
    | 0 := 0                -- if arg is 0, then 0
    | (nat.succ n') := n'   -- otherwise one less than arg

Each line starting with | gives a pattern-result
pair. Each line is |, pattern, := result. The really
fundamental idea here is that you can pull apart the
arguments while you're matching to get at value that
they incorporate. Starting from the top, Lean matches
given arguments with each pattern until one matches.
The matching process can bind names to parts of the
arguments. These names can then be used on the right
of the := to define the value of the return result. 

.. code-block:: lean

  def add2 : ℕ → ℕ := 
    fun n, nat.succ (nat.succ n) 


.. code-block:: lean

  example : sub1 0 = 0 := rfl
  example : sub1 1 = 0 := rfl
  example : sub1 2 = 1 := rfl
  example : sub1 3 = 1 := rfl  -- bad test
  example : add2 0 = 2 := rfl
  example : add2 1 = 3 := rfl
  example : add2 2 = 4 := rfl
  example : add2 3 = 6 := rfl -- bad test


.. code-block:: lean

  def sub1 (n : ℕ) : ℕ :=   -- first arg named to left of :
    match n with            -- match in Leandoes case analysis
    | 0 := 0                -- n = 0
    | (n' + 1) := n'        -- n > 0
    end
  
  def add2 (n : ℕ) := n+2   -- n+2 is short for succ(succ n)!


.. code-block:: lean

  example : sub1 0 = 0 := rfl
  example : sub1 1 = 0 := rfl
  example : sub1 2 = 1 := rfl
  example : sub1 3 = 1 := rfl  -- bad test
  example : add2 0 = 2 := rfl
  example : add2 1 = 3 := rfl
  example : add2 2 = 4 := rfl
  example : add2 3 = 6 := rfl -- bad test

