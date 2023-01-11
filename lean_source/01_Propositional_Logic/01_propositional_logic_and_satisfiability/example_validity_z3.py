from z3 import *


def isValid(P):
    s = Solver()
    s.add(Not(P))  # replace True with required declarative spec
    return (s.check() == unsat)


# Declare X to be a Z3 Bool variable
X = Bool('X')
# Print the result of testing (X Or Not X) for validity
print(isValid(Or(X, Not(X))))
# Print the result of testing (X And Not X) for validity
print(isValid(And(X, Not(X))))
