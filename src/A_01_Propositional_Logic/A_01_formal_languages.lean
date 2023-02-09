
inductive lparen 
| mk

inductive rparen
| mk


/- 
Here are some examples where we use these values.
In the first case we use *def* in Lean to bind a
value (representing a left parenthesis) to the
identifier, *a_lef_paren.* In the second case we
used *example* in Lean as a way simply to exhibit
a value of a particular type (here representing a
right parenthesis).
-/

def a_left_paren : lparen := lparen.mk
example          : rparen := rparen.mk


inductive bal 
| mk_empty
| mk_nonempty (l: lparen) (b : bal) (r : rparen) 


open bal

def b0 : bal :=       -- ∅ 
  mk_empty            

def b1 : bal :=       -- (∅)
mk_nonempty           -- constructor
  lparen.mk           -- argument left parenthesis
  b0                  -- note: we could write mk_empty
  rparen.mk           -- argument right parenthesis

def b2 :=             -- ((∅))
mk_nonempty  
  lparen.mk
  b1
  rparen.mk

def b3 :=
mk_nonempty
  lparen.mk
  (
    mk_nonempty
      lparen.mk
      (
        mk_nonempty
          lparen.mk
          mk_empty
          rparen.mk
      )
      rparen.mk
  )
  rparen.mk


#check b1


#reduce b1
#reduce b2
#reduce b3



def sem : bal → ℕ 
| mk_empty := 0
| (mk_nonempty l b r) := 1 + sem b

-- We can now run some tests to see that it works
#reduce sem b0
#reduce sem b1
#reduce sem b2

