
inductive prop_var : Type
| x
| y 
| z

open prop_var 


inductive prop_expr
| var_expr (v : prop_var)
| and_expr (e1 e2 : prop_expr)
| or_expr (e1 e2 : prop_expr)

open prop_expr


def X : prop_expr := var_expr x
def Y : prop_expr := var_expr y
def Z : prop_expr := var_expr z


def XandY : prop_expr := and_expr X Y 
def XandY_and_Z : prop_expr := and_expr XandY Z 


def all_true : prop_var → bool
| _ := tt   -- for any argument return true (tt in Lean)


def all_false : prop_var → bool
| _ := ff   -- for any argument return true (tt in Lean)


def mixed : prop_var → bool
| prop_var.x := tt
| _ := ff

#reduce mixed z

def another_interpretation : prop_var → bool
| x := tt
| y := ff
| z := tt


def prop_eval : prop_expr → (prop_var → bool) → bool 
| (var_expr v) i := i v
| (and_expr e1 e2) i := band (prop_eval e1 i) (prop_eval e2 i)
| (or_expr e1 e2) i := bor (prop_eval e1 i) (prop_eval e2 i)



#check all_true 


#reduce prop_eval X all_true
#reduce prop_eval Y all_true
#reduce prop_eval Z all_true

#reduce prop_eval X all_false
#reduce prop_eval Y all_false
#reduce prop_eval Z all_false

#reduce prop_eval XandY all_true
#reduce prop_eval XandY all_false
#reduce prop_eval XandY mixed

#reduce prop_eval (and_expr (and_expr X Y) (or_expr X Z)) mixed


