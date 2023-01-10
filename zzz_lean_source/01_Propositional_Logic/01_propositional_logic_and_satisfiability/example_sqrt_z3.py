from z3 import *

def sqrt(n):
    sqrtn = Real('sqrtn')
    s = Solver()
    # replace True with required declarative spec
    s.add(And(sqrtn**2 == n, sqrtn >= 0))
    isSat = s.check()
    if (isSat == sat):
        return s.model()
    return -1


print(sqrt(17))
