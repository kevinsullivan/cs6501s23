# Propositional logic and satisfiability exercises

## How can you check for validity in Z3

The *Solver.check* command of Z3 returns one of two answers:

- *sat* if there's at least one **interpretation** that makes the given proposition, P, true
- unsat, if there is no solution to the given proposition

What's missing is an explicit check for the *validity* of P. How can you easily use Z3 to determine if P is *valid?*

Demonstrate your insight by using Z3 to prove that for any propositional (Boolean) variable, X, the proposition "X **or** not X" is *valid.* Do this by editing the *example_validity_z3.py* file and following the instructions there.

## 2. Add declarative specification example_sqrt.py

Part 1. Copy example_sqrt.py to mywork, then complete follow the instructions in the file to complete the definition of the square root function with a declarative specification of what it means for *sqrt* to be a square root of n. Add a few test cases to convince yourself that it works.

Part 2. Make a copy of the sqrt function, calling it neg_sqrt, and update the definition to force it to return the negative square root of n, if it exists, and otherwise return -1.

## Solve a fun logic puzzle

Write a Python program using Z3 to solve the following puzzle

A crime has been committed. The police have 5 suspects at least one of whom is guilty. The suspects are Chase, Decker, Ellis, Heath, and Mullaney. The police have acertained the following facts:

- At least one of them is guilty
- if Chase is guilty and Heath is innocent, then Decker is guilty.
- if Chase is innocent, then Mullaney is innocent.
- if Heath is guilty, then Mullaney is guilty.
- Chase and Heath are not both guilty.
- Unless Heath is guilty, Decker is innocent.
  
## Solve a system of linear equations using Z3

When you take linear algebra you'll learn *procedures* for solving systems of linear equations. Write a Python program to determine (a) whether this system of equations has any solutions, and (b) print out a solution is there is at least one, otherwise to print "There are no solutions."

- 3*x + 2*y - z = 1
- 2*x + 2*y + 4*z = -2
- -x + 0.5*y - z = 0

## Solve a shape arithmetic puzzle

Here are three shape equations:

- Triangle + Square + Circle = 10
- Circle + Square - Triangle = 6
- Circle + Triangle - Square = 4

What numerical values for Triangle, Square, and Circle make all
of these equality propositions true at once?
