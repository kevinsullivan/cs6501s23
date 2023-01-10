# Ack: https://medium.com/galileo-onwards/logic-puzzle-2-74e0166a4176
# From Hy Conrad’s Giant Book of Whodunit Puzzles (1999, pg 115–6). 

from z3 import *

# We represent Guilty as a True value
# Innocent is Not Guilty, this a False value
C, D, E, H, M = Bools(["Chase", "Decker", "Ellis", "Heath","Mullaney",])

s = Solver()

# 1. At least one suspect is guilty
some_guilty = Or(C,D,H,M,E)

# 2. If Chase is guilty and 
#       Heath is innocent
#    then Decker is guilty
C_H_D = (Implies(And(C, Not(H)), D))

# 3. If Chase is innocent
#    then Mullaney is innocent
C_M = Implies(Not(C), Not(M))

# 4. If Heath is guilty
#    then Mullaney is guilty
H_M = Implies(H,M)

# 5. Chase and Heath are not both guilty
C_H = Not(And(C, H))


# 6. Unless Heath is guilty
#    then Decker is innocent
H_D = Implies(Not(H), Not(D))

# a complete specification of what counts as a solution  
# + here, of propositions, means "and"
puzzle = And(some_guilty, C_H_D, C_M, H_M, C_H, H_D)

s.add(puzzle)

# We could also have done thr following: 
# s.add(Or(C,D,H,M,E))
# s.add(Implies(And(C, Not(H)), D))
# s.add(Implies(Not(C), Not(M)))
# s.add(Implies(H,M))
# s.add(Not(And(C, H)))
# s.add(Implies(Not(H), Not(D)))

# Check for sat, if so store a model and set isSat to sat, else unsat
isSat = s.check()

if (isSat == sat) :
    print("Found a solution:\n", s.model())
else :
    print("There's no solution.")