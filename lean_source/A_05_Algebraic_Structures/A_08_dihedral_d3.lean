import .A_07_affine_spaces


namespace d3

inductive state
| f0r0
| f0r1
| f0r2
| f1r0
| f1r1
| f1r2

inductive action
| af0r0
| af0r1
| af0r2
| af1r0
| af1r1
| af1r2

open state
open action

-- want module so additive

-- stub: always return zero action
def action_mul : action → action → action 
| _ _ := af0r0    


end d3

namespace d3

-- actions
inductive dihedral : Type
| r0 : dihedral
| r1 : dihedral
| r2 : dihedral
| f0 : dihedral
| f1 : dihedral
| f2 : dihedral

open dihedral

-- 
def dihedral_mul : dihedral → dihedral → dihedral
| r0 r0 := r0
| r0 r1 := r1
| r0 r2 := r2
| r0 f0 := f0
| r0 f1 := f1
| r0 f2 := f2
| r1 r0 := r1
| r1 r1 := r2
| r1 r2 := r0
| r1 f0 := f2
| r1 f1 := f0
| r1 f2 := f1
| r2 r0 := r2
| r2 r1 := r0
| r2 r2 := r1
| r2 f0 := f1
| r2 f1 := f2
| r2 f2 := f0
| f0 r0 := f0
| f0 r1 := f1
| f0 r2 := f2
| f0 f0 := r0
| f0 f1 := r2
| f0 f2 := r1
| f1 r0 := f1
| f1 r1 := f2
| f1 r2 := f0
| f1 f0 := r1
| f1 f1 := r0
| f1 f2 := r2
| f2 r0 := f2
| f2 r1 := f0
| f2 r2 := f1
| f2 f0 := r2
| f2 f1 := r1
| f2 f2 := r0


def dihedral_inv : dihedral → dihedral
| r0 := r0
| r1 := r2
| r2 := r1
| f0 := f0
| f1 := f2
| f2 := f1

def dihedral_table : list (list dihedral) :=
[[r0, r1, r2, f0, f1, f2],
 [r1, r2, r0, f1, f2, f0],
 [r2, r0, r1, f2, f0, f1],
 [f0, f2, f1, r0, r2, r1],
 [f1, f0, f2, r2, r1, r0],
 [f2, f1, f0, r1, r0, r2]]

#eval dihedral_table

end d3
