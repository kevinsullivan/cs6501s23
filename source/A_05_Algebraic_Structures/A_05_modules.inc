
*******
Modules
*******

We've now undertood what it means to be a torsor over 
a group. A concrete example is our torsor of triangles 
over a group of rotational symmetries. That fact that
rotational symmetries form an additive group lets us 
do *additive group math* on symmetries: associative add, 
additively invert, subtract, zero left/right identity. 

In this chapter, we strengthen this concept by upgrading 
a mere additive group of actions/differences to a *module* 
of actions. In comparison with a group, G, a module adds a
set of scalars and an operation for multiplying group 
actions by scalars. 

For example, if s is a scalar and v is a group action,
then s • v is scalar multiplication of s and v yielding a
new, "scaled" group action. 

The set of scalars must form at least a *ring*, so you 
can add, invert, substract, and multiply scalars by each 
other (+, -, *). For example, the integers for a ring: 
you can multiply, add, invert, and thus subtract them,
but dividing them generally doesn't produce new integers.

If sclars have multiplicative inverses as well, and thus 
division, then you have a scalar *field*. For example, the
set of real numbers minus {0} forms a field. A module with
a scalar *field* is called a vector space.

The overall picture, then, is one in which, in a module, 
you can not only add, invert, and substract actions, but
you can also multiply (*scale*) them by scalars. Example:
if v₁ and v₂ are group actions and s₁ and s₂ are scalars,
then s₁ • (v1 +ᵥ v2) is also an action, s₁ • v₁ + s₁ • v₂; 
and (s₁ + s₂) • v1 = s• v₁ + s₁ • v₂, is too. A module is
a generalization of a vector space where you can't always 
compute inverses of scalars. 

Once we have modules, as richer sets of group actions, then
we'll be able to form torsors over *modules*. That takes us
right right up to the threshold of affine spaces, which are
simply torsors over *vector* spaces. Vector spaces are just
modules with that extra structure on their sets of scalars.


Modules in Lean
---------------

In Lean, one can form a module from an *additive commutative 
monoid* M, and a *semi-ring,* R, of scalars. A module relaxes
the need for an underlying *group* of actions by relaxing the
need for additive inverses of actions. And unlike a full ring, 
a semi-ring omits the requirement for additive inverses (and
thus subtraction) of scalars. 

Note that in a ring, the existence of additive inverses means
that 0 is a multiplicative zero (prove it to yourself); in a 
semi-ring, by contrast, without additive inverses, one has to
identify the multiplicative zero explicitly (and show that it
is one).

Example
-------

Can we turn our group of triangle rotations into a module?
What would we need? Answer: a ring of scalars and a scalar
multiplication operation. What would be a good scalar ring?
How about the integers? They do form a ring, though not a
field, as discussed. If we have a rotation action, g, and 
an integer scalar r, how would we define the scalar product,
r • g? It needs to be another action. How about the action
that simply applies g r times? 

additive commutative monoid
~~~~~~~~~~~~~~~~~~~~~~~~~~~


.. code-block:: lean

  /-
  /-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
  @[protect_proj, ancestor add_monoid add_comm_semigroup]
  class add_comm_monoid (M : Type u) extends add_monoid M, add_comm_semigroup M
  -/
  
  #check @add_comm_monoid.mk
  /-
  add_comm_monoid.mk : 
    Π {M : Type u} 
      (add : M → M → M) 
      (add_assoc : ∀ (a b c : M), a + b + c = a + (b + c)) 
      (zero : M) 
      (zero_add : ∀ (a : M), 0 + a = a) 
      (add_zero : ∀ (a : M), a + 0 = a) 
      (nsmul : ℕ → M → M), 
      auto_param (∀ (x : M), nsmul 0 x = 0) (name.mk_string "try_refl_tac" name.anonymous) → 
      auto_param (∀ (n : ℕ) (x : M), nsmul n.succ x = x + nsmul n x) (name.mk_string "try_refl_tac" name.anonymous) → 
      (∀ (a b : M), a + b = b + a) → 
      add_comm_monoid M
  -/
  
  open rot
  
  def rot_add_comm : ∀ (a b : rot), a + b = b + a :=
  begin
      assume a b,
      cases a,
      repeat {
        cases b,
        repeat {exact rfl},
      },
    end
  
  instance : add_comm_monoid rot := 
  ⟨ 
    rot_add,
    rot_add_assoc,
    r0,
    rot_left_ident,
    rot_right_ident,
    rot_npow,            -- fix multiplicative name
    rot_npow_zero,
    rot_npow_succ,
    rot_add_comm,
  ⟩ 
  
  #check @module.mk
  /-
  module.mk :
    Π {R : Type u_1} 
      {M : Type u_2} 
      [_inst_1 : semiring R] 
      [_inst_2 : add_comm_monoid M]
      [_to_distrib_mul_action : distrib_mul_action R M],
      (∀ (r s : R) (x : M), (r + s) • x = r • x + s • x) → 
      (∀ (x : M), 0 • x = 0) → 
      module R M
  -/
  
  #check @distrib_mul_action
  /-
  @[ext] class distrib_mul_action (M A : Type*) [monoid M] [add_monoid A]
    extends mul_action M A :=
  (smul_zero : ∀ (a : M), a • (0 : A) = 0)
  (smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y)
  -/
  
  #check @mul_action
  /-
  class mul_action (α : Type*) (β : Type*) [monoid α] extends has_smul α β :=
  (one_smul : ∀ b : β, (1 : α) • b = b)
  (mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)
  -/
  
  instance : has_smul ℤ rot := ⟨ rot_zpow ⟩ 
  
  lemma rot_mul_smul : ∀ (x y : ℤ) (b : rot), (x * y) • b = x • y • b := sorry
  
  instance : mul_action ℤ rot :=
  ⟨
    begin
    assume b,
    cases b,
    repeat {exact rfl},
    end,
  
    begin
    assume x y b,
    apply rot_mul_smul,       -- sorried
    end,
  ⟩
  
  lemma rot_smul_zero : ∀ (a : ℤ), a • (0 : rot) = 0 := 
  begin
  simp [rot_zpow],
  end
  
  lemma rot_smul_add : ∀ (a : ℤ) (x y : rot), a • (x + y) = a • x + a • y :=
  begin
  assume z x y,
  
  -- annoying: notation is blocking progress, use show to change notation 
  have fix : r0 = (0:rot) := begin exact rfl, end,
  
  -- by case analysis on x, y
  cases x,
  repeat {
    cases y,
    repeat {
      rw fix, 
      simp [rot_add],
    },
  },
  
  -- induction on z
  repeat {
  induction z with n negn,
  simp [rot_npow],
  simp [rot_zpow],
  },
  
  -- by commutativity of rot +
  apply rot_add_comm,
  apply rot_add_comm,
  end
  
  instance : distrib_mul_action ℤ rot :=
  ⟨
    rot_smul_zero,
    rot_smul_add,
  ⟩
  
  /-
    (∀ (r s : R) (x : M), (r + s) • x = r • x + s • x) → 
    (∀ (x : M), 0 • x = 0)
  -/
  
  instance : module ℤ rot :=
  ⟨ show ∀ (r s : ℤ) (x : rot), (r + s) • x = r • x + s • x,
    begin
    assume r s m,
    sorry,          -- oops
    end,
    begin
    assume x,
    exact rfl,
    end
  ⟩ 
  
  open tri
  #reduce ((3:ℤ) • r120) • t120
  #reduce ((-2:ℤ) • r120) • t120

