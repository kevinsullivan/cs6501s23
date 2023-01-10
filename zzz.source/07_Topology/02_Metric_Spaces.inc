.. index:: metric space

.. _metric_spaces:

Metric spaces
--------------

Examples in the previous section focus on sequences of real numbers. In this section we will go up a bit in generality and focus on 
metric spaces. A metric space is a type ``X`` equipped with a distance function ``dist : X → X → ℝ`` which is a generalization of
the function ``λ x y, |x - y|`` from the case where ``X = ℝ``.

Introducing such a space is easy and we will check all properties required from the distance function.

.. code-block:: lean

  
  variables {X : Type*} [metric_space X] (a b c : X)
  
  #check (dist a b : ℝ)
  
  #check (dist_nonneg : 0 ≤ dist a b)
  
  #check (dist_eq_zero : dist a b  = 0 ↔ a = b)
  
  #check (dist_comm a b : dist a b  = dist b a)
  
  #check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)

Note we also have variants where the distance can be infinite or where ``dist a b`` can be zero without having ``a = b`` or both.
They are called ``emetric_space``, ``pseudo_metric_space`` and ``pseudo_emetric_space`` respectively (here "e" stands for "extended").

Note that our journey from ``ℝ`` to metric spaces jumped over the special case of normed spaces that also require linear algebra and
will be explained as part of the calculus chapter.

Convergence and continuity
^^^^^^^^^^^^^^^^^^^^^^^^^^

Using distance functions, we can already define convergent sequences and continuous functions between metric spaces. 
They are actually defined in a more general setting covered in the next section,
but we have lemmas recasting the definition is terms of distances.

.. code-block:: lean

  
  example {u : ℕ → X} {a : X} : 
    tendsto u at_top (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  metric.tendsto_at_top
  
  example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} :
    continuous f ↔
    ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  metric.continuous_iff
  

.. index:: continuity, tactics ; continuity


A *lot* of lemmas have some continuity assumptions, no we end up proving a lot of continuity results and there 
is a ``continuity`` tactic devoted to this task. Let's prove a continuity statement that will be needed
in an exercise below. Notice that Lean knows how to treat a product of two metric spaces as a metric space, so
it makes sense to consider continuous functions from ``X × X`` to ``ℝ``. 
In particular the (uncurried version of the) distance function is such a function.


.. code-block:: lean

  example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) : 
    continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
  by continuity

This tactic is a bit slow, so it is also useful to know
how to do it by hand. We first need to use that ``λ p : X × X, f p.1`` is continuous because it
is the composition of ``f``, which is continuous by assumption ``hf``, and the projection ``prod.fst`` whose continuity
is the content of the lemma ``continuous_fst``. The composition property is ``continuous.comp`` which is
in the ``continuous`` namespace so we can use dot notation to compress
``continuous.comp hf continuous_fst`` into ``hf.comp continuous_fst`` which is actually more readable
since it really reads as composing our assumption and our lemma. 
We can do the same for the second component to get continuity of ``λ p : X × X, f p.2``. We then assemble
those two continuities using ``continuous.prod_mk`` to get
``(hf.comp continuous_fst).prod_mk (hf.comp continuous_snd) : continuous (λ p : X × X, (f p.1, f p.2))``
and compose once more to get our full proof.

.. code-block:: lean

  
  example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) : 
    continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
  continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))
  

The combination of ``continuous.prod_mk`` and ``continuous_dist`` via ``continuous.comp`` feels clunky,
even when heavily using dot notation as above. A more serious issue is that this nice proof requires a lot of
planning. Lean accepts the above proof term because it is a full term proving a statement which is 
definitionally equivalent to our goal, the crucial definition to unfold being that of a composition of functions. 
Indeed our target function ``λ p : X × X, dist (f p.1) (f p.2)`` is not presented as a composition. 
The proof term we provided proves continuity of ``dist ∘ (λ p : X × X, (f p.1, f p.2))`` which happens 
to be definitionally equal to our target function. But if we try to build this proof gradually using 
tactics starting with ``apply continuous_dist.comp`` then Lean's elaborator will fail to recognize a 
composition and refuse to apply this lemma. It is especially bad at this when products of types are involved.

A better lemma to apply here is 
``continuous.dist {f g : X → Y} : continuous f → continuous g → continuous (λ x, dist (f x) (g x))``
which is nicer to Lean's elaborator and also provides a shorter proof when directly providing a full 
proof term, as can be seen from the following two new proofs of the above statement:

.. code-block:: lean

  
  example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) : 
    continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
  begin
    apply continuous.dist,
    exact hf.comp continuous_fst,
    exact hf.comp continuous_snd
  end
  
  example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) : 
    continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)
  

Note that, without the elaboration issue coming from composition, another way to compress
our proof would be to use ``continuous.prod_map`` which is sometimes useful and gives
as an alternate proof term ``continuous_dist.comp (hf.prod_map hf)`` which even shorter to type.

Since it is sad to decide between a version which is better for elaboration and a version which is shorter
to type, let us wrap this discussion with a last bit of compression offered
by ``continuous.fst'`` which allows to compress ``hf.comp continuous_fst`` to ``hf.fst'`` (and the same with ``snd``) 
and get our final proof, now bordering obfuscation.


.. code-block:: lean

  example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) : 
    continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
  hf.fst'.dist hf.snd'
  

It's your turn now to prove some continuity lemma. After trying the continuity tactic, you will need 
``continuous.add``, ``continuous_pow`` and ``continuous_id`` to do it by hand.


.. code-block:: lean

  example {f : ℝ → X} (hf : continuous f) : continuous (λ x : ℝ, f (x^2 + x)) :=
  sorry
  

So far we saw continuity as a global notion, but one can also define continuity at a point. 

.. code-block:: lean

  
  example {X Y : Type*} [metric_space X] [metric_space Y] (f : X → Y) (a : X) : 
  continuous_at f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  metric.continuous_at_iff
  


Balls, open sets and closed sets
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Once we have a distance function, the most important geometric definitions are (open) balls and closed balls.


.. code-block:: lean

  
  variables r : ℝ
  
  example : metric.ball a r = {b | dist b a < r} := rfl
  
  example : metric.closed_ball a r = {b | dist b a ≤ r} := rfl
  

Note that `r` is any real number here, there is no sign restriction. Of course some statements do require a radius condition.

.. code-block:: lean

  
  example (hr : 0 < r) : a ∈ metric.ball a r := metric.mem_ball_self hr
  
  example (hr : 0 ≤ r) : a ∈ metric.closed_ball a r := metric.mem_closed_ball_self hr
  

Once we have balls, we can define open sets. They are actually defined in a more general setting covered in the next section,
but we have lemmas recasting the definition is terms of balls.


.. code-block:: lean

  example (s : set X) : is_open s ↔ ∀ x ∈ s, ∃ ε > 0, metric.ball x ε ⊆ s :=
  metric.is_open_iff
  

Then closed sets are sets whose complement is open. Their important property is they are closed under limits. The closure of a set is the smallest subset containing it.

.. code-block:: lean

  
  example {s : set X} : is_closed s ↔ is_open sᶜ :=
  is_open_compl_iff.symm
  
  example {s : set X} (hs : is_closed s) {u : ℕ → X} (hu : tendsto u at_top (𝓝 a)) 
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (eventually_of_forall hus)
  
  example {s : set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ metric.ball b ε :=
  metric.mem_closure_iff

Do the next exercise without using `mem_closure_iff_seq_limit`

.. code-block:: lean

  example {u : ℕ → X} (hu : tendsto u at_top (𝓝 a)) {s : set X} (hs : ∀ n, u n ∈ s) : 
    a ∈ closure s :=
  sorry
  


Remember from the filters sections that neighborhood filters play a big role in mathlib.
In the metric space context, the crucial point is that balls provide bases for those filters.
The main lemmas here are ``metric.nhds_basis_ball`` and ``metric.nhds_basis_closed_ball`` 
that claim this for open and closed balls with positive radius. The center point is an implicit
argument so we can invoke ``filter.has_basis.mem_iff`` as in the following example.


.. code-block:: lean

  example {x : X} {s : set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, metric.ball x ε ⊆ s :=
  metric.nhds_basis_ball.mem_iff
  
  example {x : X} {s : set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, metric.closed_ball x ε ⊆ s :=
  metric.nhds_basis_closed_ball.mem_iff
  


Compactness
^^^^^^^^^^^

Compactness is an important topological notion. It distinguishes subsets of a metric space
that enjoy the same kind of properties as segments in reals compared to other intervals:

* Any sequence taking value in a compact set has a subsequence that converges in this set
* Any continuous function on a nonempty compact set with values in real numbers is bounded and achieves its bounds somewhere (this is called the extreme values theorem).
* Compact sets are closed sets.

Let us first check that the unit interval in reals is indeed a compact set, and then check the above
claims for compact sets in general metric spaces. In the second statement we only 
need continuity on the given set so we will use ``continuous_on`` instead of ``continuous``, and
we will give separate statements for the minimum and the maximum. Of course all these results
are deduced from more general versions, some of which will be discussed in later sections.


.. code-block:: lean

  
  example : is_compact (set.Icc 0 1 : set ℝ) :=
  is_compact_Icc
  
  example {s : set X} (hs : is_compact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 a) :=
  hs.tendsto_subseq hu
  
  example {s : set X} (hs : is_compact s) (hs' : s.nonempty) 
    {f : X → ℝ} (hfs : continuous_on f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_forall_le hs' hfs
  
  example {s : set X} (hs : is_compact s) (hs' : s.nonempty) 
    {f : X → ℝ} (hfs : continuous_on f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_forall_ge hs' hfs
  
  example {s : set X} (hs : is_compact s) : is_closed s :=
  hs.is_closed
  


We can also metric spaces which are globally compact, using an extra ``Prop``-valued type class:


.. code-block:: lean

  example {X : Type*} [metric_space X] [compact_space X] : is_compact (univ : set X) :=
  compact_univ


In a compact metric space any closed set is compact, this is ``is_compact.is_closed``.

Uniformly continuous functions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We now turn to uniformity notions on metric spaces : uniformly continuous functions, Cauchy sequences and completeness.
Again those are defined in a more general context but we have lemmas in the metric name space to access their elementary definitions.
We start with uniform continuity.


.. code-block:: lean

  example {X : Type*} [metric_space X] {Y : Type*} [metric_space Y] {f : X → Y} : 
    uniform_continuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  metric.uniform_continuous_iff
  

In order to practice manipulating all those definitions, we will prove that continuous
functions from a compact metric space to a metric space are uniformly continuous 
(we will see a more general version in a later section).

We will first give an informal sketch. Let ``f : X → Y`` be a continuous function from
a compact metric space to a metric space.
We fix ``ε > 0`` and start looking for some ``δ``.

Let ``φ : X × X → ℝ := λ p, dist (f p.1) (f p.2)`` and let ``K := { p : X × X | ε ≤ φ p }``.
Observe ``φ`` is continuous since ``f`` and distance are continuous.
And ``K`` is clearly closed (use ``is_closed_le``) hence compact since ``X`` is compact.

Then we discuss two possibilities using ``eq_empty_or_nonempty``.
If ``K`` is empty then we are clearly done (we can set ``δ = 1`` for instance).
So let's assume ``K`` is not empty, and use the extreme value theorem to choose ``(x₀, x₁)`` attaining the infimum
of ``φ`` on ``K``. We can then set ``δ = dist x₀ x₁`` and check everything works.


.. code-block:: lean

  example {X : Type*} [metric_space X] [compact_space X] {Y : Type*} [metric_space Y]
    {f : X → Y} (hf : continuous f) : uniform_continuous f :=
  sorry
  

Completeness
^^^^^^^^^^^^

A Cauchy sequence in a metric space is a sequence whose terms get closer and closer to each other. 
There are a couple of equivalent ways to state that idea.
In particular converging sequences are Cauchy. The converse is true only in so-called *complete* 
spaces.



.. code-block:: lean

  
  example (u : ℕ → X) : cauchy_seq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N,  ∀ n ≥ N, dist (u m) (u n) < ε :=
  metric.cauchy_seq_iff
  
  example (u : ℕ → X) : cauchy_seq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  metric.cauchy_seq_iff'
  
  
  example [complete_space X] (u : ℕ → X) (hu : cauchy_seq u) : ∃ x, tendsto u at_top (𝓝 x) :=
  cauchy_seq_tendsto_of_complete hu
  


We'll practice using this definition by proving a convenient criterion which is a special case of a
criterion appearing in mathlib. This is also a good opportunity to practive using big sums in
a geometric context. In addition to the explanations from the filters section, you will probably need 
``tendsto_pow_at_top_nhds_0_of_lt_1``, ``tendsto.mul`` and ``dist_le_range_sum_dist``.

.. code-block:: lean

  
  lemma cauchy_seq_of_le_geometric_two' {u : ℕ → X} (hu : ∀ (n : ℕ), dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) :
    cauchy_seq u :=
  begin
    rw metric.cauchy_seq_iff',  
    intros ε ε_pos,
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε,
    { sorry },
    use N,
    intros n hn,
    obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn,
    calc dist (u (N + k)) (u N) = dist (u (N+0)) (u (N + k)) : sorry
    ... ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) : sorry
    ... ≤ ∑ i in range k, (1/2 : ℝ)^(N+i) : sorry
    ... = 1/2^N*∑ i in range k, (1 / 2) ^ i : sorry
    ... ≤ 1/2^N*2 : sorry
    ... < ε : sorry
  end


We are ready for the final boss of this section: Baire's theorem for complete metric spaces!
The proof skeleton below shows interesting techniques. It uses the ``choose`` tactic in its exclamation
mark variant (you should experiment with removing this exclamation mark) and it shows how to
define something inductively in the middle of a proof using ``nat.rec_on``.


.. code-block:: lean

  open metric
  
  example [complete_space X] (f : ℕ → set X) (ho : ∀ n, is_open (f n)) (hd : ∀ n, dense (f n)) : dense (⋂n, f n) :=
  begin
    let B : ℕ → ℝ := λ n, (1/2)^n,
    have Bpos : ∀ n, 0 < B n, sorry,
    /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closed_ball center radius` is included both in `f n` and in `closed_ball x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
    have : ∀ (n : ℕ)  (x : X) (δ > 0), ∃ (y : X) (r > 0), r ≤ B (n+1) ∧ closed_ball y r ⊆ (closed_ball x δ) ∩ f n,
    { sorry },
    choose! center radius Hpos HB Hball using this,
    intros x,
    rw mem_closure_iff_nhds_basis nhds_basis_closed_ball,
    intros ε εpos,
    /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x` belonging to all
    `f n`. For this, we construct inductively a sequence `F n = (c n, r n)` such that the closed ball
    `closed_ball (c n) (r n)` is included in the previous ball and in `f n`, and such that
    `r n` is small enough to ensure that `c n` is a Cauchy sequence. Then `c n` converges to a
    limit which belongs to all the `f n`. -/
    let F : ℕ → (X × ℝ) := λn, nat.rec_on n (prod.mk x (min ε (B 0)))
                                (λn p, prod.mk (center n p.1 p.2) (radius n p.1 p.2)),
    let c : ℕ → X := λ n, (F n).1,
    let r : ℕ → ℝ := λ n, (F n).2,
    have rpos : ∀ n, 0 < r n,
    { sorry },
    
    have rB : ∀n, r n ≤ B n,
    { sorry },
    have incl : ∀n, closed_ball (c (n+1)) (r (n+1)) ⊆ (closed_ball (c n) (r n)) ∩ (f n),
    { sorry },
    have cdist : ∀ n, dist (c n) (c (n+1)) ≤ B n,
    { sorry },
    have : cauchy_seq c, from cauchy_seq_of_le_geometric_two' cdist,
    -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
    rcases cauchy_seq_tendsto_of_complete this with ⟨y, ylim⟩,
    -- this point `y` will be the desired point. We will check that it belongs to all
    -- `f n` and to `ball x ε`.
    use y,
    have I : ∀n, ∀ m ≥ n, closed_ball (c m) (r m) ⊆ closed_ball (c n) (r n),
    { sorry },
    have yball : ∀n, y ∈ closed_ball (c n) (r n),
    { sorry },
    sorry
  end
  


