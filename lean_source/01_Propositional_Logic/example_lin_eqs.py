from z3 import *


x, y, z = Reals('x y z')

s = Solver()

C = And(
        3*x + 2*y - z == 1,
        2*x + 2*y + 4*z == -2,
        -x + 0.5*y - z == 0)

s.add(C)

if (s.check() == sat) :
    print(s.model())


# Declare X to be a Z3 Bool variable
X = Bool('X')
# Print the result of testing (X Or Not X) for validity
print(isValid(Or(X, Not(X))))
# Print the result of testing (X And Not X) for validity
print(isValid(And(X, Not(X))))
