import linear_algebra.affine_space.basic
import .A_04_torsors
import group_theory.group_action
import data.real.basic
import algebra.direct_sum.basic


abbreviation K := ℚ   -- Make K a mere alias for ℚ 





abbreviation K := ℚ            -- abstract field to make it easy to change


namespace borked

abbreviation pnt := K           -- represent points by field values
def pnt1 : pnt := (1/2:K)       -- a point represented arbitrarily by 1/2 

-- this approach does not rule out bad expressions
def bork := pnt1 + pnt1         -- oops, point-point addition makes no sense
def brok := pnt1 +ᵥ pnt1        -- oops, treating point as vector is not good
end borked


namespace borked2
def pnt := ℚ
def pnt1 : pnt := (1/2:ℚ)
def bork : pnt := pnt1 + pnt1  -- oops, operation not defined
def brok : pnt := pnt1 +ᵥ pnt1 -- oops, operation not defined
end borked2


namespace borked3
#check add_torsor ℚ 
@[derive [add_torsor ℚ]] def pnt : Type := ℚ
def pnt1 : pnt := (1/2:ℚ)
def vec := pnt1 -ᵥ pnt1   -- oh, hooray, allowed
def nope := pnt1 + pnt1   -- oh, hooray, disallowed
#check vec                -- oops, just bare rationals
end borked3



-- First we define our vector type with the right structures
@[derive [add_comm_monoid, add_group, module K, has_repr]] def vec : Type := K

-- Now we define a torsor over this vector space
@[derive [add_torsor vec, has_repr]] def pnt := K



-- define several points, initialized, as we see, by elements of K. 
def pnt1 : pnt := (1/2:K)
def pnt2 : pnt := (3/2:K)

-- We can confirm that supported operations work correctly
def vec1 := pnt2 -ᵥ pnt1                -- YAY, point-point subtraction 
def pnt3 := vec1 +ᵥ pnt2                -- YAY, action of vector on point
def pnt4 := ((2/3:ℚ) • vec1) +ᵥ pnt2      -- YAY, scalar mul (•) yields vec

-- The resulting values are correctly computed?
#eval vec1    -- expect 1
#eval pnt3    -- expect 5/2
#eval pnt4    -- expect 2/3 + 3/2 = 13/6

-- And physically meaningless operations produce type errors 
#check pnt1 + pnt1              -- oops, type error, can't add points
def vec' := pnt2 - pnt1         -- oops, type error, use torsor -ᵥ operation
def pnt' := pnt2 + vec1         -- oops, type error, use vec-point +ᵥ
def pnt'' := pnt2 +ᵥ vec1       -- oops, vector arg has to come first
def pnt''' := ((2/3:ℚ) * vec1) +ᵥ pnt1  -- oops, first term is ℚ not vec



#check @add_torsor
/-
add_torsor : 
  Π (G : out_param (Type u_1)), 
    Type u_2 → 
  Π [_inst_1 : out_param (add_group G)], 
    Type (max u_1 u_2)-/

open_locale affine
#check affine_space
/-
affine_space : 
  Π (G : out_param (Type u_1)), 
    Type u_2 → 
  Π [_inst_1 : out_param (add_group G)], 
    Type (max u_1 u_2)
-/


-- @[derive [add_torsor   vec, has_repr]] def pnt := K
-- @[derive [affine_space vec, has_repr]] def pnt := K

