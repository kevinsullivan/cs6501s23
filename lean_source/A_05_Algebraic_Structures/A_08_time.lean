import linear_algebra.affine_space.basic
import .A_04_torsors
import group_theory.group_action
import data.real.basic


/- TEXT:
In this chapter we model the physical quantity of classical time using
a rational timeline with no distinguished origin.   
TEXT. -/

-- QUOTE:
abbreviation K := ℚ            -- abstract field to make it easy to change
-- QUOTE. 

-- Our vector-valued duration type and associated structures
@[derive [add_comm_monoid, add_group, module K, has_repr]] 
def dur : Type := K

-- Now we define a torsor over this vector space
@[derive [add_torsor dur, has_repr]] def tim := K

-- examples

def thrpm : tim := (3:ℚ)
def fivpm : tim := (5:ℚ)

-- I think I just saw that - works between points
def durat' : dur := fivpm - thrpm -- KS: See this.
def durat : dur := fivpm -ᵥ thrpm -- point-point diff

def sevpm : tim :=  durat +ᵥ fivpm
#eval durat'
#eval sevpm

-- can't add points
#check thrpm + fivpm  -- no definition of + for this combination of arg types
-- QUOTE. 