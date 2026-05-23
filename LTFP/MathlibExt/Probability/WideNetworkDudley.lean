/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.CoveringNumberEuclidean
import LTFP.MathlibExt.Probability.LinearClassClosedBallCover
import LTFP.MathlibExt.Probability.LinearClassSampleCoverCard
import LTFP.MathlibExt.Probability.LinearizedRiskSampleCover
import LTFP.Foundations.DudleyEntropy
import LTFP.Foundations.Main

/-!
# Wide-network generalization carrier: linearized-risk cover from a totally-bounded parameter ball

Composes several existing ingredients on the B8 N6 wide-network
generalization path into one statement that exposes the *qualitative*
shape the Dudley entropy integral needs:

1. `covering_number_euclidean_ball` (this file's dependency) — the
   `(⌈2 √d B / δ⌉₊ + 1) ^ d` *external*-cover-cardinality bound for the
   parameter closed ball. **NOTE: this explicit cardinality is NOT yet
   composed into the carrier theorem below; see "Residual bridge".**
2. `linear_class_closed_ball_exists_finite_cover` — existence of a
   finite finset cover of the parameter ball at any positive radius.
3. `linear_class_sample_pred_card_le` — sample-prediction tuple cover
   inherits cardinality from the parameter cover.
4. `linearized_risk_class_sample_cover_of_param_cover` — parameter
   cover lifts to a `(2 B)(δ R)`-cover of squared-loss values on the
   sample.
5. `linear_predictor_lipschitz_on_ball` (transitive via 4 above).

We work entirely with internal finset covers (every cover element is
in the parameter ball). The grid construction in
`covering_number_euclidean_ball` produces *external* cover points
(corners of a bounding square that may lie slightly outside the
`L²`-ball); to land an *internal* cover with the same cardinality
bound one would have to either project the external grid back into the
ball with a Lipschitz factor, or compose a fresh "Lipschitz-image-of-
cover" lemma on LTFP's internal `coveringNumber` (see below). The
file surfaces:

- `wide_network_param_finset_cover` — *internal* finset cover at
  resolution `δ` (size existentially bounded, no explicit number).
- `wide_network_linearized_risk_explicit_cover` — the full composite
  carrier theorem in its honest current form: it produces an internal
  finset cover `C` of the parameter ball, together with the lifted
  linearized-risk sample-cover accuracy and the sample-prediction-
  tuple cardinality bound `≤ |C|`, *without* attaching an explicit
  numeric bound on `|C|`.
- `wide_network_linearized_risk_explicit_cover_card` — a *weaker*
  companion that, despite its current name, only exposes the explicit
  external-covering-number bound for the parameter ball itself; it
  does **not** lift to a linearized-risk-cover or to a sample-loss
  cover. See its docstring for the honest characterization and the
  rename note.

## Lipschitz-image-of-cover bridge (landed 0a89656 + composed below)

To feed `dudley_entropy_integral'` on the squared-loss class one needs
both (i) the lifted linearized-risk cover (provided here) AND (ii) an
explicit numeric cardinality bound for that lifted cover, expressed
on LTFP's internal `coveringNumber` (in
`LTFP/Foundations/CoveringNumber.lean`). The Lipschitz-image-of-cover
bridge `coveringNumber_image_lipschitz`
(`LTFP/Foundations/CoveringNumber.lean`, landed `0a89656`) supplies
the link

  "if `f : X → Y` is `L`-Lipschitz on `A` and `C` is an `ε`-cover of
   `A` in `X`, then `f '' C` is an `(L * ε)`-cover of `f '' A` in `Y`,
   and `coveringNumber (f '' A) (L*ε) ≤ coveringNumber A ε`"

stated on LTFP's `coveringNumber`. It is composed below with
`dudley_entropy_integral'` (`LTFP/Foundations/DudleyEntropy.lean`) to
give the end-to-end Rademacher complexity bound in terms of the
parameter-ball cover via the `wide_network_linearizedRisk_*` family of
theorems (`wide_network_linearizedRisk_covering_number_le` for the
cover bridge, `wide_network_rademacher_complexity_via_dudley` for the
Dudley-on-EFS form, and
`wide_network_rademacher_complexity_via_dudley_paramBall` for the
true end-to-end form whose Dudley integrand is itself expressed via
the parameter-ball covering number at rescaled radius `x / (2 B R)`).
-/

open scoped NNReal ENNReal RealInnerProductSpace

namespace LTFP

-- TODO(upstream-or-replace): this helper is largely redundant. Mathlib's
-- `Metric.finite_approx_of_totallyBounded`
-- (`Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`) is strictly stronger:
-- it returns a finite *Set* (immediately convertible to a `Finset`) of
-- internal centres at any positive resolution, with the same δ-cover
-- conclusion. The only thing this helper adds is the packaging into a
-- `Finset` directly and a slightly different cover predicate
-- (`dist x c ≤ δ` rather than the strict version). Future cleanup:
-- replace internal call sites with `Metric.finite_approx_of_totallyBounded`
-- plus `Set.Finite.toFinset`, then delete this lemma.
/-- Auxiliary: a `TotallyBounded` set in a `PseudoMetricSpace` admits,
for every `δ > 0`, a finite *finset* cover by points in the set itself.
A bridge from `TotallyBounded` to a usable explicit finset form.

**Note (2026-05-23 audit):** mostly redundant with
`Metric.finite_approx_of_totallyBounded` in Mathlib; kept here only
because its `Finset`-shaped conclusion is the form consumed downstream
by `wide_network_param_finset_cover`. See the `TODO(upstream-or-replace)`
comment above. -/
theorem totallyBounded_exists_finset_subset_cover
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (hA : TotallyBounded A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : Finset X, (↑C : Set X) ⊆ A ∧
      ∀ x ∈ A, ∃ c ∈ C, dist x c ≤ δ := by
  classical
  -- `Metric.totallyBounded_iff` gives a finite set of centres (possibly
  -- outside A). Filter to centres whose `δ/2`-ball meets A, pick an
  -- internal witness from each such ball, then triangle-inequality to δ.
  rcases (Metric.totallyBounded_iff.mp hA) (δ / 2) (by linarith) with
    ⟨T, hTfin, hTcov⟩
  -- Filter the finite centre set down to those that actually intersect A.
  set T_useful : Set X := {t ∈ T | (Metric.ball t (δ / 2) ∩ A).Nonempty}
  have hT_useful_fin : T_useful.Finite :=
    hTfin.subset (fun t ht => ht.1)
  -- For each useful t, the intersection is nonempty; pick a witness.
  let pickFun : X → X := fun t =>
    if h : (Metric.ball t (δ / 2) ∩ A).Nonempty then h.choose else t
  have pickFun_mem_A :
      ∀ t : X, (Metric.ball t (δ / 2) ∩ A).Nonempty → pickFun t ∈ A := by
    intro t ht
    have hchoose := ht.choose_spec
    have h_eq : pickFun t = ht.choose := by simp [pickFun, ht]
    rw [h_eq]; exact hchoose.2
  have pickFun_close :
      ∀ t : X, (Metric.ball t (δ / 2) ∩ A).Nonempty →
        dist (pickFun t) t < δ / 2 := by
    intro t ht
    have hchoose := ht.choose_spec
    have h_eq : pickFun t = ht.choose := by simp [pickFun, ht]
    rw [h_eq]
    have : ht.choose ∈ Metric.ball t (δ / 2) := hchoose.1
    simpa [Metric.mem_ball] using this
  -- Build C from the *filtered* centre set image.
  let C : Finset X := hT_useful_fin.toFinset.image pickFun
  refine ⟨C, ?_, ?_⟩
  · -- C ⊆ A
    intro c hc
    have hc_mem : c ∈ hT_useful_fin.toFinset.image pickFun := by exact_mod_cast hc
    rcases Finset.mem_image.mp hc_mem with ⟨t, ht_in, h_eq⟩
    have ht_useful : t ∈ T_useful :=
      (Set.Finite.mem_toFinset hT_useful_fin).mp ht_in
    have : pickFun t ∈ A := pickFun_mem_A t ht_useful.2
    rw [← h_eq]; exact this
  · -- Every point of A is within δ of some element of C.
    intro x hx
    have hx_in : x ∈ ⋃ y ∈ T, Metric.ball y (δ / 2) := hTcov hx
    rw [Set.mem_iUnion₂] at hx_in
    rcases hx_in with ⟨t, ht_T, hx_ball⟩
    have ht_inter : (Metric.ball t (δ / 2) ∩ A).Nonempty := ⟨x, hx_ball, hx⟩
    have ht_useful : t ∈ T_useful := ⟨ht_T, ht_inter⟩
    refine ⟨pickFun t, ?_, ?_⟩
    · have ht_finset : t ∈ hT_useful_fin.toFinset :=
        (Set.Finite.mem_toFinset hT_useful_fin).mpr ht_useful
      exact Finset.mem_image.mpr ⟨t, ht_finset, rfl⟩
    · -- dist x (pick t) ≤ dist x t + dist t (pick t) ≤ δ/2 + δ/2 = δ.
      have h1 : dist x t < δ / 2 := by simpa [Metric.mem_ball] using hx_ball
      have h2 : dist t (pickFun t) < δ / 2 := by
        rw [dist_comm]; exact pickFun_close t ht_inter
      have htri : dist x (pickFun t) ≤ dist x t + dist t (pickFun t) :=
        dist_triangle _ _ _
      linarith

/-- The parameter closed ball of radius `B` in `EuclideanSpace ℝ (Fin d)`
admits, at every resolution `δ > 0`, a finite finset of *internal* cover
points (each `θ` in the ball is `δ`-close to some `c` in the cover).
Convenience wrapper combining `linear_class_closed_ball_totallyBounded`
with the totally-bounded-to-finset extractor. -/
theorem wide_network_param_finset_cover
    {d : ℕ} (B δ : ℝ) (hδ : 0 < δ) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin d)),
      (∀ c ∈ C, ‖c‖ ≤ B) ∧
      (∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B → ∃ c ∈ C, ‖θ - c‖ ≤ δ) := by
  classical
  have hTB : TotallyBounded
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B) :=
    linear_class_closed_ball_totallyBounded (d := d) B
  rcases totallyBounded_exists_finset_subset_cover hTB hδ with
    ⟨C, hC_sub, hCcov⟩
  refine ⟨C, ?_, ?_⟩
  · intro c hc
    have hc_in : c ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B :=
      hC_sub (by exact_mod_cast hc)
    simpa [Metric.mem_closedBall, dist_zero_right] using hc_in
  · intro θ hθ
    have hθ_in : θ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hθ
    rcases hCcov θ hθ_in with ⟨c, hcC, hdist⟩
    refine ⟨c, hcC, ?_⟩
    simpa [dist_eq_norm] using hdist

/-- **Wide-network generalization carrier (Option A pre-Dudley): honest
form.**

For a wide linear-predictor class indexed by the closed parameter ball
`‖θ‖ ≤ B_param` in `EuclideanSpace ℝ (Fin d)`, a bounded sample
`‖xs i‖ ≤ R`, targets `ys`, and uniform prediction-error bound `B`,
there exists a *finite finset* `C` of cover parameters such that:

* every `θ` in the parameter ball has a `c ∈ C` with the *linearized
  risk* values `(⟨θ, xs i⟩ - ys i)^2 ↔ (⟨c, xs i⟩ - ys i)^2` agreeing to
  within `(2 B)(δ R)` on every sample index `i`;
* `c` itself is in the parameter ball (so the cover element satisfies
  the same prediction-error bound that `θ` does, modulo
  `linear_predictor_lipschitz_on_ball`), and the induced
  prediction-tuple finset has cardinality `≤ |C|`.

**Honest scope (2026-05-23 audit):** this theorem produces the finite
finset `C` from `TotallyBounded`ness of the parameter ball (via
`wide_network_param_finset_cover`); it does **NOT** attach the
explicit Euclidean cardinality bound `|C| ≤ (⌈2 √d B_param / δ⌉₊ + 1)^d`
from `covering_number_euclidean_ball`. The explicit cardinality lives
on an *external* grid cover and would need a Lipschitz-image-of-cover
bridge (see the module docstring's "Residual bridge" section) before
it can be attached to this `C`. Downstream consumers that need the
explicit number must currently invoke
`wide_network_linearized_risk_explicit_cover_card` separately for the
parameter-ball cardinality and combine it by hand. -/
theorem wide_network_linearized_risk_explicit_cover
    {d m : ℕ}
    (xs : Fin m → EuclideanSpace ℝ (Fin d))
    (ys : Fin m → ℝ)
    (B_param δ R B : ℝ)
    (hδ : 0 < δ)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hbound_all :
      ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
        ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin d)),
      -- All cover elements live inside the parameter ball.
      (∀ c ∈ C, ‖c‖ ≤ B_param) ∧
      -- Sample-prediction-tuple cover cardinality inherits from |C|.
      (C.image
          (fun c => fun i : Fin m => inner ℝ c (xs i))).card ≤ C.card ∧
      -- For every θ in the parameter ball, some c ∈ C approximates
      -- θ in linearized squared-loss values on every sample point.
      (∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
        ∃ c ∈ C,
          ∀ i : Fin m,
            |(inner ℝ θ (xs i) - ys i) ^ 2 - (inner ℝ c (xs i) - ys i) ^ 2|
              ≤ (2 * B) * (δ * R)) := by
  classical
  -- Step (1): extract an internal δ-finset-cover of the parameter ball.
  rcases wide_network_param_finset_cover (d := d) B_param δ hδ with
    ⟨C, hC_norm, hC_cover⟩
  refine ⟨C, hC_norm, Finset.card_image_le, ?_⟩
  -- Step (2): lift the cover via linearized-risk Lipschitz to a sample cover.
  set Θ : Set (EuclideanSpace ℝ (Fin d)) :=
    {θ | ‖θ‖ ≤ B_param} with hΘ_def
  set Cset : Set (EuclideanSpace ℝ (Fin d)) :=
    (C : Set (EuclideanSpace ℝ (Fin d))) with hCset_def
  -- Re-express the cover hypothesis on these sets.
  have hcover : ∀ θ ∈ Θ, ∃ c ∈ Cset, ‖θ - c‖ ≤ δ := by
    intro θ hθ
    rcases hC_cover θ hθ with ⟨c, hcC, hdist⟩
    exact ⟨c, by exact_mod_cast hcC, hdist⟩
  -- The uniform prediction-error bound applies to every θ ∈ Θ.
  have hbound : ∀ θ ∈ Θ, ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B := by
    intro θ hθ i
    exact hbound_all θ hθ i
  -- It also applies to every c ∈ Cset (since C ⊆ parameter ball).
  have hboundC : ∀ c ∈ Cset, ∀ i : Fin m, |inner ℝ c (xs i) - ys i| ≤ B := by
    intro c hc i
    have hc_finset : c ∈ C := by exact_mod_cast hc
    exact hbound_all c (hC_norm c hc_finset) i
  -- Apply the linearized-risk sample-cover composition (ingredient 4).
  have hLifted :=
    linearized_risk_class_sample_cover_of_param_cover (d := d) (m := m)
      Θ Cset xs ys δ R B hx hcover hbound hboundC
  intro θ hθ
  rcases hLifted θ hθ with ⟨c, hcCset, h_acc⟩
  exact ⟨c, by exact_mod_cast hcCset, h_acc⟩

/-- **Parameter-ball external covering-number bound (honest form).**

**Misleading historical name (2026-05-23 audit):** despite the suffix
`linearized_risk_..._cover_card`, this theorem does **not** mention
`ys`, the squared loss, the sample-prediction tuple cover, or the
linearized-risk-class cover at all. It is literally just
`covering_number_euclidean_ball` (the external cardinality bound for
the parameter ball) packaged together with the trivial restatement of
the sample bound `∀ θ ..., ‖xs i‖ ≤ R`. The honest name for what is
actually proved here is `wide_network_param_ball_external_cover_card`;
the current name is retained to avoid breaking any out-of-tree callers
but is scheduled for rename.

What this theorem ACTUALLY proves, for `d ≥ 1`, `B_param ≥ 0`, and
`δ : ℝ≥0` positive:

1. **First conjunct:** the *external* covering number of the
   parameter ball `Metric.closedBall 0 B_param ⊆ EuclideanSpace ℝ (Fin d)`
   at resolution `δ` is at most `(⌈2 √d B_param / δ⌉₊ + 1) ^ d`.
2. **Second conjunct:** the sample bound `‖xs i‖ ≤ R` (trivially
   re-quantified over `θ`).

What this theorem does **NOT** prove (despite the historical name):

- No linearized-risk cover is constructed.
- No sample-prediction-tuple cover is constructed.
- No squared-loss accuracy guarantee is stated.
- The targets `ys` are not even a hypothesis.
- The bound uses *external* covering points which need not live in
  the parameter ball; lifting them to an internal finset cover (the
  form `wide_network_linearized_risk_explicit_cover` uses) requires
  the Lipschitz-image-of-cover bridge noted in the module docstring.

Composing this cardinality bound with
`wide_network_linearized_risk_explicit_cover` to obtain a single
Dudley-input statement is the residual bridge work. -/
theorem wide_network_linearized_risk_explicit_cover_card
    {d m : ℕ}
    (xs : Fin m → EuclideanSpace ℝ (Fin d))
    (B_param : ℝ) (δ : ℝ≥0) (hd : 1 ≤ d) (hB_param : 0 ≤ B_param)
    (hδ_ne : δ ≠ 0)
    (R : ℝ) (hx : ∀ i : Fin m, ‖xs i‖ ≤ R) :
    Metric.externalCoveringNumber δ
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param) ≤
      ((⌈2 * Real.sqrt d * B_param / (δ : ℝ)⌉₊ + 1 : ℕ) ^ d : ℕ) ∧
    -- Sample-prediction-tuple cardinality inherits: same upper bound
    -- applies to any internal finset cover of the parameter ball.
    (∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
      ∀ i : Fin m, ‖xs i‖ ≤ R) := by
  refine ⟨?_, fun _ _ _ => hx _⟩
  exact covering_number_euclidean_ball d B_param δ hd hB_param hδ_ne

/-! ### §35 closure: Rademacher complexity via Dudley + Lipschitz cover bridge

Composes `coveringNumber_image_lipschitz` (from
`LTFP/Foundations/CoveringNumber.lean`) with `dudley_entropy_integral'`
(from `LTFP/Foundations/DudleyEntropy.lean`) and the parameter-ball
Lipschitz constant for the linearized squared-loss class. The result
is a Dudley bound on the empirical Rademacher complexity of the
linearized-risk class, indexed by the closed parameter ball, with the
covering-number integrand controlled by the parameter-ball covering
number through the Lipschitz scale `2 B R`.

The B8 N6 wide-network bridge composition that §35 left as a residual
gap closes end-to-end with this theorem. -/

section ClosureViaDudley

/-- Linearized squared-loss family indexed by the closed parameter
ball. The "data point" type is `EuclideanSpace ℝ (Fin d) × ℝ`, packaging
inputs `x` and targets `y` together so that `F θ (x, y) = (⟨θ, x⟩ - y)²`
is a single-argument function suitable for the
`EmpiricalFunctionSpace` machinery. -/
private noncomputable def linearizedRiskFamily
    {d : ℕ} (B_param : ℝ) :
    {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param} →
      EuclideanSpace ℝ (Fin d) × ℝ → ℝ :=
  fun θ p => (inner ℝ θ.val p.1 - p.2) ^ 2

/-- The sample for the linearized-risk family: package inputs and targets. -/
private def linearizedRiskSample
    {d m : ℕ} (xs : Fin m → EuclideanSpace ℝ (Fin d))
    (ys : Fin m → ℝ) :
    Fin m → EuclideanSpace ℝ (Fin d) × ℝ :=
  fun i => (xs i, ys i)

/-- Lipschitz constant for the parameter-to-EFS embedding of the
linearized-risk family. Numerically `2 * B * R`, packaged into `ℝ≥0`
via `Real.toNNReal`. -/
private noncomputable def linearizedRiskLipConst (B R : ℝ) : ℝ≥0 :=
  Real.toNNReal (2 * B * R)

/-- Auxiliary: empirical norm bounded by sample-wise max. -/
private lemma empiricalNorm_le_of_pointwise_bound
    {𝒳 : Type*} {m : ℕ} (S : Fin m → 𝒳) (f : 𝒳 → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ i, |f (S i)| ≤ M) :
    empiricalNorm S f ≤ M := by
  classical
  unfold empiricalNorm
  by_cases hm : m = 0
  · subst hm
    simp
    exact hM
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hinv_nn : (0 : ℝ) ≤ (1 : ℝ) / (m : ℝ) := by positivity
  -- Each term ≤ M^2
  have hsum_le : (∑ i : Fin m, (f (S i)) ^ 2) ≤ (m : ℝ) * M ^ 2 := by
    have hbnd : ∀ i ∈ Finset.univ, (f (S i)) ^ 2 ≤ M ^ 2 := by
      intro i _
      have : |f (S i)| ≤ M := hbound i
      have hsq : |f (S i)| ^ 2 ≤ M ^ 2 := by
        have h0 : 0 ≤ |f (S i)| := abs_nonneg _
        exact pow_le_pow_left₀ h0 this 2
      simpa [sq_abs] using hsq
    have := Finset.sum_le_sum hbnd
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this
  have hprod_le : (1 : ℝ) / (m : ℝ) * (∑ i : Fin m, (f (S i)) ^ 2) ≤ M ^ 2 := by
    have hstep := mul_le_mul_of_nonneg_left hsum_le hinv_nn
    have hrw : (1 : ℝ) / (m : ℝ) * ((m : ℝ) * M ^ 2) = M ^ 2 := by
      field_simp
    linarith [hstep, hrw.le, hrw.ge]
  calc Real.sqrt ((1 / (m : ℝ)) * ∑ i : Fin m, (f (S i)) ^ 2)
      ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt hprod_le
    _ = M := by
        rw [Real.sqrt_sq hM]

/-- The parameter-to-EFS embedding of the linearized-risk family is
Lipschitz with constant `2 B R`. Stated abstractly on the subtype
`{θ // ‖θ‖ ≤ B_param}`. -/
private theorem linearizedRiskEmbedding_lipschitz
    {d m : ℕ} (xs : Fin m → EuclideanSpace ℝ (Fin d))
    (ys : Fin m → ℝ)
    (B_param R B : ℝ)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hbound :
      ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
        ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B) :
    LipschitzWith (linearizedRiskLipConst B R)
      (fun θ : {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param} =>
        (⟨θ⟩ : EmpiricalFunctionSpace
          (linearizedRiskFamily (d := d) B_param)
          (linearizedRiskSample xs ys))) := by
  classical
  refine LipschitzWith.of_dist_le_mul ?_
  intro θ θ'
  -- Unfold the EFS distance to the empirical norm of the squared-loss difference.
  show empiricalDist (linearizedRiskSample xs ys)
        (linearizedRiskFamily (d := d) B_param θ)
        (linearizedRiskFamily (d := d) B_param θ')
      ≤ ((linearizedRiskLipConst B R : ℝ≥0) : ℝ) * dist θ θ'
  -- Use the linearized-risk pointwise Lipschitz bound.
  have hθ_bound : ∀ i, |inner ℝ θ.val (xs i) - ys i| ≤ B :=
    hbound θ.val θ.property
  have hθ'_bound : ∀ i, |inner ℝ θ'.val (xs i) - ys i| ≤ B :=
    hbound θ'.val θ'.property
  -- Pointwise bound on the difference of squared losses.
  have hpoint : ∀ i,
      |(inner ℝ θ.val (xs i) - ys i) ^ 2 - (inner ℝ θ'.val (xs i) - ys i) ^ 2|
        ≤ (2 * B * R) * ‖θ.val - θ'.val‖ := by
    intro i
    have h1 := linearized_risk_lipschitz_param θ.val θ'.val (xs i) (ys i) B R
                (hx i) (hθ_bound i) (hθ'_bound i)
    -- h1 : |...| ≤ (2 * B) * (‖θ.val - θ'.val‖ * R)
    calc |(inner ℝ θ.val (xs i) - ys i) ^ 2 - (inner ℝ θ'.val (xs i) - ys i) ^ 2|
        ≤ (2 * B) * (‖θ.val - θ'.val‖ * R) := h1
      _ = (2 * B * R) * ‖θ.val - θ'.val‖ := by ring
  -- empiricalDist S (F θ) (F θ') = empiricalNorm S (F θ - F θ').
  rw [empiricalDist_def]
  -- 2 * B * R ≥ 0 needed for the bound.
  have hLnn : 0 ≤ 2 * B * R := by positivity
  -- Bound the empirical norm by the sample-wise max.
  have hsample_bnd : ∀ i,
      |((linearizedRiskFamily (d := d) B_param θ) -
        (linearizedRiskFamily (d := d) B_param θ'))
        ((linearizedRiskSample xs ys) i)|
      ≤ (2 * B * R) * ‖θ.val - θ'.val‖ := by
    intro i
    -- Unfold definitions.
    show |(linearizedRiskFamily (d := d) B_param θ ((linearizedRiskSample xs ys) i))
          - (linearizedRiskFamily (d := d) B_param θ' ((linearizedRiskSample xs ys) i))|
        ≤ (2 * B * R) * ‖θ.val - θ'.val‖
    simp only [linearizedRiskFamily, linearizedRiskSample]
    exact hpoint i
  have hM_nn : 0 ≤ (2 * B * R) * ‖θ.val - θ'.val‖ :=
    mul_nonneg hLnn (norm_nonneg _)
  have hEnorm :
      empiricalNorm (linearizedRiskSample xs ys)
        ((linearizedRiskFamily (d := d) B_param θ) -
          (linearizedRiskFamily (d := d) B_param θ'))
      ≤ (2 * B * R) * ‖θ.val - θ'.val‖ :=
    empiricalNorm_le_of_pointwise_bound _ _ _ hM_nn hsample_bnd
  -- Convert dist θ θ' to ‖θ.val - θ'.val‖.
  have hdist_eq : dist θ θ' = ‖θ.val - θ'.val‖ := by
    rw [Subtype.dist_eq]
    exact dist_eq_norm _ _
  -- Convert the NNReal coercion.
  have hLcoe : ((linearizedRiskLipConst B R : ℝ≥0) : ℝ) = 2 * B * R := by
    unfold linearizedRiskLipConst
    rw [Real.coe_toNNReal _ hLnn]
  calc empiricalNorm (linearizedRiskSample xs ys)
        ((linearizedRiskFamily (d := d) B_param θ) -
          (linearizedRiskFamily (d := d) B_param θ'))
      ≤ (2 * B * R) * ‖θ.val - θ'.val‖ := hEnorm
    _ = ((linearizedRiskLipConst B R : ℝ≥0) : ℝ) * dist θ θ' := by
        rw [hLcoe, hdist_eq]

/-- The closed parameter ball, viewed as a subtype, has totally-bounded
universal set. -/
private theorem param_ball_subtype_univ_totallyBounded
    {d : ℕ} (B_param : ℝ) :
    TotallyBounded
      (Set.univ : Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}) := by
  classical
  -- Split on whether the ball is empty (B_param < 0) or contains 0.
  by_cases hB : (0 : ℝ) ≤ B_param
  · -- 0 is in the ball; subtype is nonempty. Argue via δ/2 refinement.
    have h0 : ‖(0 : EuclideanSpace ℝ (Fin d))‖ ≤ B_param := by simpa using hB
    have hTB : TotallyBounded
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param) :=
      linear_class_closed_ball_totallyBounded (d := d) B_param
    rw [Metric.totallyBounded_iff] at hTB ⊢
    intro δ hδ
    rcases hTB (δ/2) (by linarith) with ⟨T, hTfin, hTcov⟩
    set P : EuclideanSpace ℝ (Fin d) → Prop := fun t =>
      (Metric.ball t (δ/2) ∩
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param).Nonempty
    let pickFun : EuclideanSpace ℝ (Fin d) →
        {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param} := fun t =>
      if h : P t then
        ⟨h.choose, by
          have := h.choose_spec.2
          simpa [Metric.mem_closedBall, dist_zero_right] using this⟩
      else ⟨0, h0⟩
    refine ⟨pickFun '' T, hTfin.image _, ?_⟩
    intro q _hq
    have hqball : q.val ∈ Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin d)) B_param := by
      simpa [Metric.mem_closedBall, dist_zero_right] using q.property
    have hin := hTcov hqball
    rw [Set.mem_iUnion₂] at hin
    rcases hin with ⟨t, htT, hqt⟩
    have hPt : P t := ⟨q.val, hqt, hqball⟩
    refine Set.mem_iUnion₂.mpr ⟨pickFun t, Set.mem_image_of_mem _ htT, ?_⟩
    -- dist q (pickFun t) < δ via triangle.
    have hpick_val : (pickFun t).val = hPt.choose := by
      simp only [pickFun, dif_pos hPt]
    have h1 : dist q.val t < δ/2 := by simpa [Metric.mem_ball] using hqt
    have h2 : dist hPt.choose t < δ/2 := by
      have hchoose := hPt.choose_spec.1
      simpa [Metric.mem_ball] using hchoose
    have hdistq : dist q (pickFun t) = dist q.val (pickFun t).val :=
      Subtype.dist_eq _ _
    rw [Metric.mem_ball, hdistq, hpick_val]
    calc dist q.val hPt.choose
        ≤ dist q.val t + dist t hPt.choose := dist_triangle _ _ _
      _ = dist q.val t + dist hPt.choose t := by rw [dist_comm t]
      _ < δ/2 + δ/2 := by linarith
      _ = δ := by ring
  · -- B_param < 0: the subtype is empty.
    push_neg at hB
    have hEmpty :
        IsEmpty {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param} := by
      refine ⟨fun ⟨θ, hθ⟩ => ?_⟩
      have h0 : (0 : ℝ) ≤ ‖θ‖ := norm_nonneg _
      linarith
    -- Set.univ of an empty type is empty.
    have huniv_empty :
        (Set.univ : Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}) = ∅ :=
      Set.eq_empty_of_isEmpty _
    rw [huniv_empty]
    exact totallyBounded_empty

/-- The image of the parameter-ball subtype universe under the
EFS-embedding is exactly the universal set of the EFS, since EFS
elements are completely determined by their `index`. -/
private theorem efs_univ_eq_image
    {d m : ℕ} (B_param : ℝ)
    (xs : Fin m → EuclideanSpace ℝ (Fin d)) (ys : Fin m → ℝ) :
    (Set.univ : Set (EmpiricalFunctionSpace
      (linearizedRiskFamily (d := d) B_param)
      (linearizedRiskSample xs ys))) =
    (fun θ : {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param} =>
      (⟨θ⟩ : EmpiricalFunctionSpace
        (linearizedRiskFamily (d := d) B_param)
        (linearizedRiskSample xs ys))) ''
      (Set.univ : Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}) := by
  ext q
  refine ⟨fun _ => ?_, fun _ => Set.mem_univ _⟩
  exact ⟨q.index, Set.mem_univ _, by cases q; rfl⟩

/-- TotallyBoundedness of the EFS universe for the linearized-risk
family, obtained as the Lipschitz image of the totally-bounded
parameter-ball subtype. -/
private theorem linearizedRisk_efs_univ_totallyBounded
    {d m : ℕ} (xs : Fin m → EuclideanSpace ℝ (Fin d))
    (ys : Fin m → ℝ)
    (B_param R B : ℝ)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hbound :
      ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
        ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B) :
    TotallyBounded
      (Set.univ : Set (EmpiricalFunctionSpace
        (linearizedRiskFamily (d := d) B_param)
        (linearizedRiskSample xs ys))) := by
  have hTB := param_ball_subtype_univ_totallyBounded (d := d) B_param
  have hLip := linearizedRiskEmbedding_lipschitz xs ys B_param R B
                hR_nn hB_nn hx hbound
  have hImg := hTB.image hLip.uniformContinuous
  rw [efs_univ_eq_image (d := d) (m := m) B_param xs ys]
  exact hImg

/-- **B8 N6 closure helper: covering-number bridge via Lipschitz embedding.**

For any positive `ε`, the covering number of the EFS-universe for the
linearized-risk family at scale `(2 B R) · ε` is bounded above by the
covering number of the parameter-ball subtype at scale `ε`. This is
the explicit invocation of `coveringNumber_image_lipschitz` on the
parameter-to-EFS embedding, with Lipschitz constant `2 B R`.

This is the §35 "Lipschitz-image-of-cover" bridge: it lets Dudley's
integrand `√(log (coveringNumber h' x))` over the EFS universe be
controlled by `√(log (coveringNumber (param ball TB) (x/(2 B R))))`,
where the parameter-ball covering number admits the explicit
`(⌈2 √d B_param ε⁻¹⌉₊ + 1) ^ d` bound from
`covering_number_euclidean_ball`. -/
theorem wide_network_linearizedRisk_covering_number_le
    {d m : ℕ} (xs : Fin m → EuclideanSpace ℝ (Fin d))
    (ys : Fin m → ℝ)
    (B_param R B : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hbound :
      ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
        ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B) :
    coveringNumber
        (linearizedRisk_efs_univ_totallyBounded xs ys B_param R B
          hR_nn hB_nn hx hbound)
        (((linearizedRiskLipConst B R : ℝ≥0) : ℝ) * ε)
      ≤ coveringNumber
          (param_ball_subtype_univ_totallyBounded (d := d) B_param) ε := by
  classical
  -- Apply the Lipschitz cover bridge to the parameter-to-EFS embedding.
  have hLip := linearizedRiskEmbedding_lipschitz xs ys B_param R B
                hR_nn hB_nn hx hbound
  have hTB := param_ball_subtype_univ_totallyBounded (d := d) B_param
  have hbridge :=
    coveringNumber_image_lipschitz (ha := hTB) (hf := hLip) (hε := hε)
  -- `coveringNumber` for two proofs of `TotallyBounded` on the same set
  -- agrees by proof irrelevance (the `TotallyBounded` argument is a Prop).
  -- The underlying sets coincide by `efs_univ_eq_image`.
  have _hImg_eq := efs_univ_eq_image (d := d) (m := m) B_param xs ys
  have hcvn_eq :
      coveringNumber (linearizedRisk_efs_univ_totallyBounded xs ys B_param R B
          hR_nn hB_nn hx hbound)
        (((linearizedRiskLipConst B R : ℝ≥0) : ℝ) * ε) =
      coveringNumber (hTB.image hLip.uniformContinuous)
        (((linearizedRiskLipConst B R : ℝ≥0) : ℝ) * ε) := by
    congr 1
  rw [hcvn_eq]; exact hbridge

/-- **B8 N6 closure (Option A): Rademacher complexity via Dudley +
Lipschitz cover bridge.**

For a wide linear-predictor class indexed by the closed parameter ball
`‖θ‖ ≤ B_param` in `EuclideanSpace ℝ (Fin d)`, sample inputs `xs i`
bounded by `R`, targets `ys`, uniform prediction-error bound `B`, and
empirical-norm bound `c` on the linearized risk, the empirical
Rademacher complexity of the linearized-risk class is bounded by
Dudley's integral with the integrand controlled by the parameter-ball
covering number at the rescaled radius `(2 B R)⁻¹ · x`. Closes the §35
residual gap by composing `coveringNumber_image_lipschitz` with
`dudley_entropy_integral'`. -/
theorem wide_network_rademacher_complexity_via_dudley
    {d m : ℕ}
    (xs : Fin m → EuclideanSpace ℝ (Fin d)) (ys : Fin m → ℝ)
    (B_param R B c ε : ℝ)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B) (hB_param_nn : 0 ≤ B_param)
    (hε_pos : 0 < ε) (hm_pos : 0 < m) (hεc : ε < c / 2)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hbound :
      ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
        ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B)
    (hcs : ∀ θ : {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param},
      empiricalNorm (linearizedRiskSample xs ys)
        (linearizedRiskFamily (d := d) B_param θ) ≤ c) :
    let h' := linearizedRisk_efs_univ_totallyBounded xs ys B_param R B
                hR_nn hB_nn hx hbound
    empiricalRademacherComplexity_without_abs m
        (linearizedRiskFamily (d := d) B_param)
        (linearizedRiskSample xs ys) ≤
      (4 * ε + (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber h' x)))) := by
  -- Nonemptiness of the parameter-ball subtype (needed for Dudley).
  haveI : Nonempty {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param} :=
    ⟨⟨0, by simpa using hB_param_nn⟩⟩
  intro h'
  exact dudley_entropy_integral' hε_pos h' hm_pos hcs hεc

/-- **B8 N6 true end-to-end closure: Rademacher complexity bounded by a
Dudley integral over the parameter-ball covering number.**

Composes `wide_network_linearizedRisk_covering_number_le` (the
Lipschitz-image-of-cover bridge specialised to the parameter-to-EFS
embedding) with `wide_network_rademacher_complexity_via_dudley` (the
Dudley bound for the linearized-risk EFS), substituting the EFS
covering number under the integrand with the parameter-ball covering
number at the rescaled radius `x / (2 B R)`. This is the end-to-end
B8 N6 closure: the empirical Rademacher complexity of the
linearized-risk class is bounded by a Dudley integral whose
integrand is `√(log (coveringNumber (param-ball) (x / (2 B R))))`,
which itself admits the explicit Euclidean cardinality bound
`(⌈2 √d B_param / (x/(2 B R))⌉₊ + 1)^d` via
`covering_number_euclidean_ball`.

The Lipschitz constant `2 B R` must be strictly positive (`hBR_pos`)
so that `(2 B R) · (x / (2 B R)) = x` and the open-ball-scaling step
in `coveringNumber_image_lipschitz` does not collapse. -/
theorem wide_network_rademacher_complexity_via_dudley_paramBall
    {d m : ℕ}
    (xs : Fin m → EuclideanSpace ℝ (Fin d)) (ys : Fin m → ℝ)
    (B_param R B c ε : ℝ)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B) (hB_param_nn : 0 ≤ B_param)
    (hBR_pos : 0 < 2 * B * R)
    (hε_pos : 0 < ε) (hm_pos : 0 < m) (hεc : ε < c / 2)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hbound :
      ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
        ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B)
    (hcs : ∀ θ : {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param},
      empiricalNorm (linearizedRiskSample xs ys)
        (linearizedRiskFamily (d := d) B_param θ) ≤ c) :
    empiricalRademacherComplexity_without_abs m
        (linearizedRiskFamily (d := d) B_param)
        (linearizedRiskSample xs ys) ≤
      (4 * ε + (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber
              (param_ball_subtype_univ_totallyBounded (d := d) B_param)
              (x / (2 * B * R)))))) := by
  classical
  -- Nonemptiness of the parameter-ball subtype.
  haveI hNE : Nonempty {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param} :=
    ⟨⟨0, by simpa using hB_param_nn⟩⟩
  -- Standard names.
  set L : ℝ := 2 * B * R with hL_def
  have hL_pos : 0 < L := hBR_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  set h' := linearizedRisk_efs_univ_totallyBounded xs ys B_param R B
              hR_nn hB_nn hx hbound with hh'_def
  set hTB := param_ball_subtype_univ_totallyBounded (d := d) B_param with hTB_def
  -- Step (1): apply Dudley to get the EFS-integrand bound.
  have hDudley :
      empiricalRademacherComplexity_without_abs m
          (linearizedRiskFamily (d := d) B_param)
          (linearizedRiskSample xs ys) ≤
        (4 * ε + (12 / Real.sqrt m) *
          (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (coveringNumber h' x)))) := by
    have := wide_network_rademacher_complexity_via_dudley xs ys
              B_param R B c ε hR_nn hB_nn hB_param_nn hε_pos hm_pos hεc
              hx hbound hcs
    -- The Dudley theorem returns the same shape; unfold the `let`.
    simpa using this
  -- Step (2): pointwise bound on the integrand over `[ε, c/2]`.
  -- For each x ∈ [ε, c/2], `coveringNumber h' x ≤ coveringNumber hTB (x/L)`
  -- via the Lipschitz cover bridge (specialised to ε' := x/L), and the
  -- result lifts through `Real.log` and `Real.sqrt`.
  have hε_le_half : ε ≤ c / 2 := le_of_lt hεc
  -- L coercion (NNReal → ℝ) for the Lipschitz cover bridge call.
  have hLcoe : ((linearizedRiskLipConst B R : ℝ≥0) : ℝ) = L := by
    unfold linearizedRiskLipConst L
    rw [Real.coe_toNNReal _ (le_of_lt hL_pos)]
  -- Pointwise bound: `√(log (cN h' x)) ≤ √(log (cN hTB (x/L)))` on Icc ε (c/2).
  have hpoint :
      ∀ x ∈ Set.Icc ε (c / 2),
        √(Real.log (coveringNumber h' x)) ≤
          √(Real.log (coveringNumber hTB (x / L))) := by
    intro x hx_mem
    have hx_pos : 0 < x := lt_of_lt_of_le hε_pos hx_mem.1
    have hxL_pos : 0 < x / L := div_pos hx_pos hL_pos
    -- Apply Lipschitz cover bridge at ε' := x / L.
    have hbridge :=
      wide_network_linearizedRisk_covering_number_le (d := d) (m := m) xs ys
        B_param R B (x / L) hxL_pos hR_nn hB_nn hx hbound
    -- Coercion conversion in the LHS scale:
    -- ((linearizedRiskLipConst B R : ℝ≥0) : ℝ) * (x / L) = L * (x / L) = x.
    have hLcalc : ((linearizedRiskLipConst B R : ℝ≥0) : ℝ) * (x / L) = x := by
      rw [hLcoe, mul_div_cancel₀ _ hL_ne]
    rw [hLcalc] at hbridge
    -- Now hbridge : coveringNumber h' x ≤ coveringNumber hTB (x / L).
    -- Lift to nonneg-log via Real.log_le_log.
    -- Need 0 < (coveringNumber h' x : ℝ).
    have h_h'_pos :
        0 < (coveringNumber h' x : ℝ) := by
      -- h' is TotallyBounded of `Set.univ` of a Nonempty subtype, so cN ≥ 1.
      have hnonemp : (Set.univ :
          Set (EmpiricalFunctionSpace
            (linearizedRiskFamily (d := d) B_param)
            (linearizedRiskSample xs ys))).Nonempty := by
        haveI := hNE
        exact ⟨⟨Classical.arbitrary _⟩, Set.mem_univ _⟩
      have := coveringNumber_nonzero hnonemp h' hx_pos
      exact_mod_cast this
    have h_param_pos :
        0 < (coveringNumber hTB (x / L) : ℝ) := by
      have hnonemp_param :
          (Set.univ :
            Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}).Nonempty :=
        ⟨⟨0, by simpa using hB_param_nn⟩, Set.mem_univ _⟩
      have := coveringNumber_nonzero hnonemp_param hTB hxL_pos
      exact_mod_cast this
    have h_param_pos' :
        0 < (coveringNumber hTB (x / L) : ℝ) := h_param_pos
    have h_h'_le_param :
        (coveringNumber h' x : ℝ) ≤
          (coveringNumber hTB (x / L) : ℝ) := by
      exact_mod_cast hbridge
    have h_log_mono :
        Real.log (coveringNumber h' x) ≤
          Real.log (coveringNumber hTB (x / L)) :=
      Real.log_le_log h_h'_pos h_h'_le_param
    exact Real.sqrt_le_sqrt h_log_mono
  -- Step (3): integral monotonicity. Need both sides interval-integrable on [ε, c/2].
  -- LHS (EFS integrand) is antitone (the existing Dudley proof shows this).
  -- RHS (param-ball integrand) is also antitone: x ↦ x/L increasing, cN is
  -- antitone in scale, log is monotone, sqrt is monotone — composing reverses
  -- order once.
  -- Nonemptiness witnesses (for `coveringNumber_nonzero` inside antitone proofs).
  have hnonemp_h' :
      (Set.univ :
        Set (EmpiricalFunctionSpace
          (linearizedRiskFamily (d := d) B_param)
          (linearizedRiskSample xs ys))).Nonempty := by
    haveI := hNE
    exact ⟨⟨Classical.arbitrary _⟩, Set.mem_univ _⟩
  have hnonemp_param :
      (Set.univ :
        Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}).Nonempty :=
    ⟨⟨0, by simpa using hB_param_nn⟩, Set.mem_univ _⟩
  -- Antitone-on for the LHS integrand on the uIcc.
  have h_uIcc_eq : Set.uIcc ε (c / 2) = Set.Icc ε (c / 2) := by
    have : min ε (c / 2) = ε ∧ max ε (c / 2) = c / 2 := by
      refine ⟨?_, ?_⟩
      · exact min_eq_left hε_le_half
      · exact max_eq_right hε_le_half
    simp [Set.uIcc, this.1, this.2]
  have h_LHS_antitoneOn :
      AntitoneOn (fun x : ℝ =>
        √(Real.log (coveringNumber h' x))) (Set.uIcc ε (c / 2)) := by
    rw [h_uIcc_eq]
    have hsqrt_mono : Monotone (fun x : ℝ => √x) := fun _ _ => Real.sqrt_le_sqrt
    apply Monotone.comp_antitoneOn hsqrt_mono
    refine antitoneOn_iff_forall_lt.mpr ?_
    intro a ha b hb hab
    have ha_pos : 0 < a := lt_of_lt_of_le hε_pos ha.1
    have hb_pos : 0 < b := lt_of_lt_of_le hε_pos hb.1
    apply Real.log_le_log
    · exact_mod_cast coveringNumber_nonzero hnonemp_h' h' hb_pos
    · exact_mod_cast
        converingNumber_antitone h' (by simp [ha_pos]) (by simp [hb_pos]) (le_of_lt hab)
  -- Antitone-on for the RHS integrand on the uIcc.
  have h_RHS_antitoneOn :
      AntitoneOn (fun x : ℝ =>
        √(Real.log (coveringNumber hTB (x / L)))) (Set.uIcc ε (c / 2)) := by
    rw [h_uIcc_eq]
    have hsqrt_mono : Monotone (fun x : ℝ => √x) := fun _ _ => Real.sqrt_le_sqrt
    apply Monotone.comp_antitoneOn hsqrt_mono
    refine antitoneOn_iff_forall_lt.mpr ?_
    intro a ha b hb hab
    have ha_pos : 0 < a := lt_of_lt_of_le hε_pos ha.1
    have hb_pos : 0 < b := lt_of_lt_of_le hε_pos hb.1
    have haL_pos : 0 < a / L := div_pos ha_pos hL_pos
    have hbL_pos : 0 < b / L := div_pos hb_pos hL_pos
    have habL : a / L ≤ b / L := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hL_pos)
      exact le_of_lt hab
    apply Real.log_le_log
    · exact_mod_cast coveringNumber_nonzero hnonemp_param hTB hbL_pos
    · exact_mod_cast
        converingNumber_antitone hTB (by simp [haL_pos]) (by simp [hbL_pos]) habL
  have hLHS_intInt :
      IntervalIntegrable
        (fun x : ℝ => √(Real.log (coveringNumber h' x)))
        MeasureTheory.volume ε (c / 2) :=
    AntitoneOn.intervalIntegrable h_LHS_antitoneOn
  have hRHS_intInt :
      IntervalIntegrable
        (fun x : ℝ => √(Real.log (coveringNumber hTB (x / L))))
        MeasureTheory.volume ε (c / 2) :=
    AntitoneOn.intervalIntegrable h_RHS_antitoneOn
  -- Apply integral_mono_on.
  have hintegral_mono :
      (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber h' x))) ≤
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber hTB (x / L)))) :=
    intervalIntegral.integral_mono_on hε_le_half hLHS_intInt hRHS_intInt hpoint
  -- Step (4): combine everything via `linarith` + nonnegativity of `12/√m`.
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hSqrtm_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_real_pos
  have hCoef_nn : 0 ≤ 12 / Real.sqrt m := by positivity
  have hScaled_le :
      (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber h' x))) ≤
      (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber hTB (x / L)))) :=
    mul_le_mul_of_nonneg_left hintegral_mono hCoef_nn
  calc empiricalRademacherComplexity_without_abs m
        (linearizedRiskFamily (d := d) B_param)
        (linearizedRiskSample xs ys)
      ≤ 4 * ε + (12 / Real.sqrt m) *
          (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (coveringNumber h' x))) := hDudley
    _ ≤ 4 * ε + (12 / Real.sqrt m) *
          (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (coveringNumber hTB (x / L)))) := by linarith

/-- **B8 N6 with-abs end-to-end closure: with-abs Rademacher complexity
bounded by a Dudley integral over the parameter-ball covering number.**

The with-abs analogue of
`wide_network_rademacher_complexity_via_dudley_paramBall`. Composes
`dudley_entropy_integral_bound_with_abs` (which contributes a factor of
`2` inside the log to account for negation-closure of the EFS) with
`wide_network_linearizedRisk_covering_number_le` (the Lipschitz-image-of-
cover bridge specialised to the parameter-to-EFS embedding), substituting
the EFS covering number under the integrand with the parameter-ball
covering number at the rescaled radius `x / (2 B R)`.

The uniform-boundedness constant for the squared-loss family is `B²`:
under the hypothesis `hbound : ∀ θ, ‖θ‖ ≤ B_param → ∀ i, |⟨θ, xs i⟩ - ys i| ≤ B`,
the squared residual `(⟨θ, xs i⟩ - ys i)²` is at most `B²` pointwise.

Downstream this theorem is consumed by the symmetrisation chain via
`uniform_deviation_expectation_le_two_smul_rademacher_complexity`
(which bounds `E[uniformDeviation]` by `2 · rademacherComplexity` with
the *with-abs* convention used by LTFP's `rademacherComplexity`). -/
theorem wide_network_rademacher_complexity_with_abs_via_dudley_paramBall
    {d m : ℕ}
    (xs : Fin m → EuclideanSpace ℝ (Fin d)) (ys : Fin m → ℝ)
    (B_param R B c ε : ℝ)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B) (hB_param_nn : 0 ≤ B_param)
    (hBR_pos : 0 < 2 * B * R)
    (hε_pos : 0 < ε) (hm_pos : 0 < m) (hεc : ε < c / 2)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hbound :
      ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
        ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B)
    (hcs : ∀ θ : {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param},
      empiricalNorm (linearizedRiskSample xs ys)
        (linearizedRiskFamily (d := d) B_param θ) ≤ c) :
    empiricalRademacherComplexity m
        (linearizedRiskFamily (d := d) B_param)
        (linearizedRiskSample xs ys) ≤
      (4 * ε + (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber
              (param_ball_subtype_univ_totallyBounded (d := d) B_param)
              (x / (2 * B * R)) : ℝ))))) := by
  classical
  -- Nonemptiness of the parameter-ball subtype.
  haveI hNE : Nonempty {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param} :=
    ⟨⟨0, by simpa using hB_param_nn⟩⟩
  -- Standard names.
  set L : ℝ := 2 * B * R with hL_def
  have hL_pos : 0 < L := hBR_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  set h' := linearizedRisk_efs_univ_totallyBounded xs ys B_param R B
              hR_nn hB_nn hx hbound with hh'_def
  set hTB := param_ball_subtype_univ_totallyBounded (d := d) B_param with hTB_def
  -- The uniform-boundedness constant: `|F θ (S j)| = |(⟨θ, xs j⟩ - ys j)²| ≤ B²`.
  have hC_bound :
      ∀ (i : {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param})
        (j : Fin m),
        |linearizedRiskFamily (d := d) B_param i
          (linearizedRiskSample xs ys j)| ≤ B ^ 2 := by
    intro θ j
    -- |F θ (xs j, ys j)| = |(⟨θ.val, xs j⟩ - ys j)²|
    have habs := hbound θ.val θ.property j
    show |(inner ℝ θ.val (xs j) - ys j) ^ 2| ≤ B ^ 2
    -- (⟨θ.val, xs j⟩ - ys j)² ≥ 0, so |·| = ·.
    have h_sq_nn : 0 ≤ (inner ℝ θ.val (xs j) - ys j) ^ 2 := sq_nonneg _
    rw [abs_of_nonneg h_sq_nn]
    -- (⟨θ.val, xs j⟩ - ys j)² = |⟨θ.val, xs j⟩ - ys j|²
    rw [← sq_abs (inner ℝ θ.val (xs j) - ys j)]
    have h0_abs : 0 ≤ |inner ℝ θ.val (xs j) - ys j| := abs_nonneg _
    exact pow_le_pow_left₀ h0_abs habs 2
  -- Step (1): apply the with-abs Dudley bound to the linearized-risk EFS.
  have hDudley :
      empiricalRademacherComplexity m
          (linearizedRiskFamily (d := d) B_param)
          (linearizedRiskSample xs ys) ≤
        (4 * ε + (12 / Real.sqrt m) *
          (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (2 * (coveringNumber h' x : ℝ))))) :=
    dudley_entropy_integral_bound_with_abs (C := B ^ 2) hC_bound
      hε_pos h' hm_pos hcs hεc
  -- Step (2): pointwise bound on the integrand over `[ε, c/2]`.
  -- For each x ∈ [ε, c/2], `coveringNumber h' x ≤ coveringNumber hTB (x/L)`
  -- via the Lipschitz cover bridge; lifts through `2 *`, `Real.log`, `Real.sqrt`.
  have hε_le_half : ε ≤ c / 2 := le_of_lt hεc
  -- L coercion (NNReal → ℝ).
  have hLcoe : ((linearizedRiskLipConst B R : ℝ≥0) : ℝ) = L := by
    unfold linearizedRiskLipConst L
    rw [Real.coe_toNNReal _ (le_of_lt hL_pos)]
  -- Pointwise bound on the integrand.
  have hpoint :
      ∀ x ∈ Set.Icc ε (c / 2),
        √(Real.log (2 * (coveringNumber h' x : ℝ))) ≤
          √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ))) := by
    intro x hx_mem
    have hx_pos : 0 < x := lt_of_lt_of_le hε_pos hx_mem.1
    have hxL_pos : 0 < x / L := div_pos hx_pos hL_pos
    -- Apply Lipschitz cover bridge at ε' := x / L.
    have hbridge :=
      wide_network_linearizedRisk_covering_number_le (d := d) (m := m) xs ys
        B_param R B (x / L) hxL_pos hR_nn hB_nn hx hbound
    -- ((linearizedRiskLipConst B R : ℝ≥0) : ℝ) * (x / L) = L * (x / L) = x.
    have hLcalc : ((linearizedRiskLipConst B R : ℝ≥0) : ℝ) * (x / L) = x := by
      rw [hLcoe, mul_div_cancel₀ _ hL_ne]
    rw [hLcalc] at hbridge
    -- Now hbridge : coveringNumber h' x ≤ coveringNumber hTB (x / L).
    have h_h'_pos :
        0 < (coveringNumber h' x : ℝ) := by
      have hnonemp : (Set.univ :
          Set (EmpiricalFunctionSpace
            (linearizedRiskFamily (d := d) B_param)
            (linearizedRiskSample xs ys))).Nonempty := by
        haveI := hNE
        exact ⟨⟨Classical.arbitrary _⟩, Set.mem_univ _⟩
      have := coveringNumber_nonzero hnonemp h' hx_pos
      exact_mod_cast this
    have h_param_pos :
        0 < (coveringNumber hTB (x / L) : ℝ) := by
      have hnonemp_param :
          (Set.univ :
            Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}).Nonempty :=
        ⟨⟨0, by simpa using hB_param_nn⟩, Set.mem_univ _⟩
      have := coveringNumber_nonzero hnonemp_param hTB hxL_pos
      exact_mod_cast this
    have h_h'_le_param :
        (coveringNumber h' x : ℝ) ≤
          (coveringNumber hTB (x / L) : ℝ) := by
      exact_mod_cast hbridge
    -- Multiply by 2 (preserves order, both sides positive).
    have h_two_h'_pos : (0 : ℝ) < 2 * (coveringNumber h' x : ℝ) := by
      positivity
    have h_two_le :
        2 * (coveringNumber h' x : ℝ) ≤
          2 * (coveringNumber hTB (x / L) : ℝ) := by
      linarith
    have h_log_mono :
        Real.log (2 * (coveringNumber h' x : ℝ)) ≤
          Real.log (2 * (coveringNumber hTB (x / L) : ℝ)) :=
      Real.log_le_log h_two_h'_pos h_two_le
    exact Real.sqrt_le_sqrt h_log_mono
  -- Step (3): integral monotonicity. Need both sides interval-integrable on [ε, c/2].
  -- Nonemptiness witnesses.
  have hnonemp_h' :
      (Set.univ :
        Set (EmpiricalFunctionSpace
          (linearizedRiskFamily (d := d) B_param)
          (linearizedRiskSample xs ys))).Nonempty := by
    haveI := hNE
    exact ⟨⟨Classical.arbitrary _⟩, Set.mem_univ _⟩
  have hnonemp_param :
      (Set.univ :
        Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}).Nonempty :=
    ⟨⟨0, by simpa using hB_param_nn⟩, Set.mem_univ _⟩
  have h_uIcc_eq : Set.uIcc ε (c / 2) = Set.Icc ε (c / 2) := by
    have : min ε (c / 2) = ε ∧ max ε (c / 2) = c / 2 := by
      refine ⟨?_, ?_⟩
      · exact min_eq_left hε_le_half
      · exact max_eq_right hε_le_half
    simp [Set.uIcc, this.1, this.2]
  -- Antitone-on for the LHS integrand on the uIcc.
  have h_LHS_antitoneOn :
      AntitoneOn (fun x : ℝ =>
        √(Real.log (2 * (coveringNumber h' x : ℝ)))) (Set.uIcc ε (c / 2)) := by
    rw [h_uIcc_eq]
    have hsqrt_mono : Monotone (fun x : ℝ => √x) := fun _ _ => Real.sqrt_le_sqrt
    apply Monotone.comp_antitoneOn hsqrt_mono
    refine antitoneOn_iff_forall_lt.mpr ?_
    intro a ha b hb hab
    have ha_pos : 0 < a := lt_of_lt_of_le hε_pos ha.1
    have hb_pos : 0 < b := lt_of_lt_of_le hε_pos hb.1
    have hcN_b_pos : (0 : ℝ) < (coveringNumber h' b : ℝ) := by
      exact_mod_cast coveringNumber_nonzero hnonemp_h' h' hb_pos
    have hcN_le : (coveringNumber h' b : ℝ) ≤ (coveringNumber h' a : ℝ) := by
      exact_mod_cast
        converingNumber_antitone h' (by simp [ha_pos]) (by simp [hb_pos])
          (le_of_lt hab)
    have h_two_b_pos : (0 : ℝ) < 2 * (coveringNumber h' b : ℝ) := by positivity
    have h_two_le : 2 * (coveringNumber h' b : ℝ) ≤
        2 * (coveringNumber h' a : ℝ) := by linarith
    exact Real.log_le_log h_two_b_pos h_two_le
  -- Antitone-on for the RHS integrand on the uIcc.
  have h_RHS_antitoneOn :
      AntitoneOn (fun x : ℝ =>
        √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ)))) (Set.uIcc ε (c / 2)) := by
    rw [h_uIcc_eq]
    have hsqrt_mono : Monotone (fun x : ℝ => √x) := fun _ _ => Real.sqrt_le_sqrt
    apply Monotone.comp_antitoneOn hsqrt_mono
    refine antitoneOn_iff_forall_lt.mpr ?_
    intro a ha b hb hab
    have ha_pos : 0 < a := lt_of_lt_of_le hε_pos ha.1
    have hb_pos : 0 < b := lt_of_lt_of_le hε_pos hb.1
    have haL_pos : 0 < a / L := div_pos ha_pos hL_pos
    have hbL_pos : 0 < b / L := div_pos hb_pos hL_pos
    have habL : a / L ≤ b / L := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hL_pos)
      exact le_of_lt hab
    have hcN_b_pos : (0 : ℝ) < (coveringNumber hTB (b / L) : ℝ) := by
      exact_mod_cast coveringNumber_nonzero hnonemp_param hTB hbL_pos
    have hcN_le : (coveringNumber hTB (b / L) : ℝ) ≤
        (coveringNumber hTB (a / L) : ℝ) := by
      exact_mod_cast
        converingNumber_antitone hTB (by simp [haL_pos]) (by simp [hbL_pos]) habL
    have h_two_b_pos : (0 : ℝ) < 2 * (coveringNumber hTB (b / L) : ℝ) := by
      positivity
    have h_two_le : 2 * (coveringNumber hTB (b / L) : ℝ) ≤
        2 * (coveringNumber hTB (a / L) : ℝ) := by linarith
    exact Real.log_le_log h_two_b_pos h_two_le
  have hLHS_intInt :
      IntervalIntegrable
        (fun x : ℝ => √(Real.log (2 * (coveringNumber h' x : ℝ))))
        MeasureTheory.volume ε (c / 2) :=
    AntitoneOn.intervalIntegrable h_LHS_antitoneOn
  have hRHS_intInt :
      IntervalIntegrable
        (fun x : ℝ => √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ))))
        MeasureTheory.volume ε (c / 2) :=
    AntitoneOn.intervalIntegrable h_RHS_antitoneOn
  have hintegral_mono :
      (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber h' x : ℝ)))) ≤
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ)))) :=
    intervalIntegral.integral_mono_on hε_le_half hLHS_intInt hRHS_intInt hpoint
  -- Step (4): combine via nonnegativity of `12 / √m`.
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hSqrtm_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_real_pos
  have hCoef_nn : 0 ≤ 12 / Real.sqrt m := by positivity
  have hScaled_le :
      (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber h' x : ℝ)))) ≤
      (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ)))) :=
    mul_le_mul_of_nonneg_left hintegral_mono hCoef_nn
  calc empiricalRademacherComplexity m
        (linearizedRiskFamily (d := d) B_param)
        (linearizedRiskSample xs ys)
      ≤ 4 * ε + (12 / Real.sqrt m) *
          (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (2 * (coveringNumber h' x : ℝ)))) := hDudley
    _ ≤ 4 * ε + (12 / Real.sqrt m) *
          (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ)))) := by linarith

/-- Composition of the wide-network Dudley-parameter-ball bound with the
symmetrization factor of `2`.

Multiplying `wide_network_rademacher_complexity_via_dudley_paramBall` by `2`
gives the explicit RHS that appears as an upper bound on the expected
supremum of (empirical − true risk) over the linearized-risk class for any
i.i.d. sample whose realised inputs/targets satisfy the deterministic
hypotheses `hx`, `hbound`, `hcs`.

Concretely, this theorem is the deterministic-sample form: it bounds
`2 · empiricalRademacherComplexity_without_abs m F S` by twice the
parameter-ball Dudley integral. The standard symmetrization identity
`μⁿ[uniformDeviation n F μ X (X ∘ ω)] ≤ 2 • rademacherComplexity n F μ X`
(`LTFP.Foundations.Main.uniform_deviation_expectation_le_two_smul_rademacher_complexity`,
line 28) supplies the missing measure-theoretic step that lifts a per-sample
Rademacher bound to a sample-averaged expected-sup bound. Composing the two
facts on an i.i.d. wide-network sample whose realisations a.s. satisfy
`hx, hbound, hcs` recovers the textbook
`E[sup_θ (R̂_S(θ) − R(θ))] ≤ 2 · (Dudley integral)` form for the linearised
squared-loss class. That measure-theoretic lift is a separate downstream
slot and is **not** discharged here; this theorem provides only the
deterministic-sample upper bound that the lift consumes.

The `2 *` placement matches the convention of
`uniform_deviation_expectation_le_two_smul_rademacher_complexity`:
the factor of `2` is on the Rademacher complexity side, not on the
Dudley integrand. -/
theorem wide_network_two_rademacher_complexity_via_dudley_paramBall
    {d m : ℕ}
    (xs : Fin m → EuclideanSpace ℝ (Fin d)) (ys : Fin m → ℝ)
    (B_param R B c ε : ℝ)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B) (hB_param_nn : 0 ≤ B_param)
    (hBR_pos : 0 < 2 * B * R)
    (hε_pos : 0 < ε) (hm_pos : 0 < m) (hεc : ε < c / 2)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hbound :
      ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
        ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B)
    (hcs : ∀ θ : {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param},
      empiricalNorm (linearizedRiskSample xs ys)
        (linearizedRiskFamily (d := d) B_param θ) ≤ c) :
    2 * empiricalRademacherComplexity_without_abs m
        (linearizedRiskFamily (d := d) B_param)
        (linearizedRiskSample xs ys) ≤
      2 * (4 * ε + (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber
              (param_ball_subtype_univ_totallyBounded (d := d) B_param)
              (x / (2 * B * R)))))) := by
  have hbase :=
    wide_network_rademacher_complexity_via_dudley_paramBall
      (d := d) (m := m) xs ys B_param R B c ε
      hR_nn hB_nn hB_param_nn hBR_pos hε_pos hm_pos hεc hx hbound hcs
  have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
  exact mul_le_mul_of_nonneg_left hbase h2_nn

/-- B8 N6 — Abstract i.i.d.-measure parameterised lift of the
deterministic wide-network Rademacher bound.

Composes `wide_network_two_rademacher_complexity_via_dudley_paramBall`
(deterministic, per-sample) with a `ν`-almost-everywhere bundle of the
linearised-risk wide-network hypotheses (`hx`, `hbound`, `hcs`) to
obtain a sample-averaged (i.e. expected over `ν`) upper bound on
`2 * empiricalRademacherComplexity_without_abs`. The RHS is the same
deterministic Dudley-integral expression as in
`wide_network_two_rademacher_complexity_via_dudley_paramBall`, lifted
verbatim — it does not depend on the realised sample `S` because the
Dudley integrand only sees `d, m, B_param, R, B, c, ε`.

## Honest scope (Option B in the dispatch sheet)

This theorem deliberately takes the sample measure `ν` as an abstract
probability measure on `Fin m → (EuclideanSpace ℝ (Fin d) × ℝ)`, with
the wide-network hypotheses bundled as a single `ν`-a.e. statement and
the LHS integrability assumed as a hypothesis (`hint`). It does **not**:

* construct the i.i.d. measure on `[−R,R]^d × [−B_Y, B_Y]` from scratch;
* derive the integrability of the empirical Rademacher complexity from
  the wide-network hypotheses (it could in principle be derived from
  the bounded-loss bound `B²`, but doing so cleanly requires a
  measurability lemma for `empiricalRademacherComplexity_without_abs`
  in the product variable, which is not yet in LTFP/Foundations);
* connect to the *with-abs* `rademacherComplexity` from
  `LTFP/Foundations/Defs.lean:38` — the standard symmetrisation argument
  in `LTFP.Foundations.Main.uniform_deviation_expectation_le_two_smul_rademacher_complexity`
  bounds `E[uniformDeviation]` by `2 • rademacherComplexity` *with*
  absolute values inside the sup, whereas the Dudley chain in
  `LTFP/Foundations/DudleyEntropy.lean` bounds the *without-abs*
  variant. The remaining gap is the with-abs Dudley analogue, which
  is downstream of this theorem and not discharged here.

What this theorem *does* provide is the cleanest verifiable bridge
between the deterministic per-sample Dudley bound and a
measure-theoretic expectation bound: the RHS is sample-independent, so
once you have the per-sample deterministic bound a.s., integration is
just `integral_mono_ae` against a constant.

The hypothesis bundle `hae` is the natural a.e.-version of the
deterministic theorem's `(hx, hbound, hcs)` triple, rephrased to live
on the pair-valued sample `S : Fin m → EuclideanSpace ℝ (Fin d) × ℝ`.
For an i.i.d. measure obtained as `ν = (μ_x ⊗ μ_y)^m` with `μ_x`
supported on the closed `R`-ball and `μ_y` supported on the closed
`B_Y`-ball, `hae` holds with `ν`-probability one once one verifies
the deterministic bounds on the supports — that verification is the
remaining piece for full Option A and is genuine measure-theoretic
plumbing not yet in LTFP/Foundations.

The factor `2` placement matches
`uniform_deviation_expectation_le_two_smul_rademacher_complexity`. -/
theorem wide_network_expected_two_rademacher_le_dudley_paramBall_of_ae
    {d m : ℕ}
    (ν : MeasureTheory.Measure (Fin m → EuclideanSpace ℝ (Fin d) × ℝ))
    [MeasureTheory.IsProbabilityMeasure ν]
    (B_param R B c ε : ℝ)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B) (hB_param_nn : 0 ≤ B_param)
    (hBR_pos : 0 < 2 * B * R)
    (hε_pos : 0 < ε) (hm_pos : 0 < m) (hεc : ε < c / 2)
    (hae :
      ∀ᵐ (S : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) ∂ν,
        (∀ i, ‖(S i).1‖ ≤ R) ∧
        (∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
          ∀ i, |@inner ℝ _ _ θ (S i).1 - (S i).2| ≤ B) ∧
        (∀ θ : {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param},
          empiricalNorm (linearizedRiskSample (fun i => (S i).1) (fun i => (S i).2))
            (linearizedRiskFamily (d := d) B_param θ) ≤ c))
    (hint : MeasureTheory.Integrable
      (fun S : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        2 * empiricalRademacherComplexity_without_abs m
              (linearizedRiskFamily (d := d) B_param) S) ν) :
    ∫ S, 2 * empiricalRademacherComplexity_without_abs m
            (linearizedRiskFamily (d := d) B_param) S ∂ν ≤
      2 * (4 * ε + (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber
              (param_ball_subtype_univ_totallyBounded (d := d) B_param)
              (x / (2 * B * R)))))) := by
  classical
  -- Abbreviation for the deterministic Dudley RHS (sample-independent).
  set DudleyRHS : ℝ :=
    2 * (4 * ε + (12 / Real.sqrt m) *
      (∫ (x : ℝ) in ε..(c/2),
        √(Real.log (coveringNumber
            (param_ball_subtype_univ_totallyBounded (d := d) B_param)
            (x / (2 * B * R)))))) with hDudleyRHS_def
  -- Pointwise a.e. bound: for ν-a.e. S, the deterministic theorem applies.
  have hae_bound :
      (fun S : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
          2 * empiricalRademacherComplexity_without_abs m
                (linearizedRiskFamily (d := d) B_param) S)
        ≤ᵐ[ν] (fun _ => DudleyRHS) := by
    filter_upwards [hae] with S hS
    obtain ⟨hx_S, hbound_S, hcs_S⟩ := hS
    -- Reconstruct xs, ys from S and apply the deterministic theorem.
    set xs : Fin m → EuclideanSpace ℝ (Fin d) := fun i => (S i).1 with hxs_def
    set ys : Fin m → ℝ := fun i => (S i).2 with hys_def
    have hS_eq : S = linearizedRiskSample xs ys := by
      funext i
      simp [linearizedRiskSample, xs, ys]
    have hbase :=
      wide_network_two_rademacher_complexity_via_dudley_paramBall
        (d := d) (m := m) xs ys B_param R B c ε
        hR_nn hB_nn hB_param_nn hBR_pos hε_pos hm_pos hεc
        hx_S hbound_S hcs_S
    -- Rewrite S as linearizedRiskSample xs ys to match the deterministic bound.
    rw [hS_eq]
    exact hbase
  -- Integrate.
  have hConst_int : MeasureTheory.Integrable
      (fun _ : Fin m → EuclideanSpace ℝ (Fin d) × ℝ => DudleyRHS) ν :=
    MeasureTheory.integrable_const _
  have hstep1 : ∫ S, 2 * empiricalRademacherComplexity_without_abs m
                  (linearizedRiskFamily (d := d) B_param) S ∂ν ≤
                ∫ _ : Fin m → EuclideanSpace ℝ (Fin d) × ℝ, DudleyRHS ∂ν :=
    MeasureTheory.integral_mono_ae hint hConst_int hae_bound
  have hstep2 : ∫ _ : Fin m → EuclideanSpace ℝ (Fin d) × ℝ, DudleyRHS ∂ν = DudleyRHS := by
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ]
    simp
  linarith [hstep1, hstep2.le, hstep2.ge]

/-! ### Closed-form endpoint bound on the wide-network Dudley integral

The wide-network Dudley integrals produced by
`wide_network_rademacher_complexity_via_dudley_paramBall` (without-abs)
and `wide_network_rademacher_complexity_with_abs_via_dudley_paramBall`
(with-abs) take the form

  `∫ x in ε..(c/2), √(Real.log (cN · (x / L)))`           -- without-abs
  `∫ x in ε..(c/2), √(Real.log (2 * cN · (x / L)))`       -- with-abs

with `L = 2 * B * R`. The map `x ↦ √(log (· cN (x/L)))` is *antitone* on
`[ε, c/2]` because (a) `x ↦ x/L` is monotone, (b) `coveringNumber hTB`
is antitone on `Set.Ioi 0`, and (c) `Real.log` and `Real.sqrt` are
monotone. Bounding the integrand pointwise by its value at the lower
endpoint `ε` yields the closed-form upper bound

  `(c/2 - ε) * √(Real.log (cN · (ε / L)))`                 -- without-abs
  `(c/2 - ε) * √(Real.log (2 * cN · (ε / L)))`             -- with-abs

These are *not* asymptotic rates — they are honest constant-factor
bounds at the lower endpoint. To turn either into a polynomial rate one
composes with the external Euclidean cardinality
`coveringNumber hTB δ ≤ (⌈2 √d B_param / δ⌉₊ + 1) ^ d` (a separate
TotallyBounded-internal-vs-external-cover bridge, currently a residual
slot — see the module docstring's "Lipschitz-image-of-cover" note).
That composition is downstream of this theorem.

These two lemmas are the cleanest closed-form bound the
paramBall-Dudley integrals admit without that residual bridge. -/

/-- **Closed-form endpoint bound on the without-abs wide-network Dudley
integral** (Option C in the dispatch sheet).

For the Dudley integrand produced by
`wide_network_rademacher_complexity_via_dudley_paramBall`, the integral
on `[ε, c/2]` is bounded above by `(c/2 - ε)` times the integrand at
the lower endpoint `ε`. The argument is just antitone-on the integrand
(monotone composition of `Real.sqrt ∘ Real.log` with the strictly
positive antitone-in-scale covering number, against the monotone
rescaling `x ↦ x / (2 B R)`) plus `intervalIntegral.integral_mono_on`
against a constant majorant.

The covering-number positivity uses `Nonempty` of the parameter-ball
subtype (via `hB_param_nn : 0 ≤ B_param`, putting `0` in the ball).
The Lipschitz scale `2 B R` must be positive (`hBR_pos`) so the
endpoint `ε / (2 B R)` is positive. -/
theorem wide_network_dudley_integral_paramBall_endpoint_bound
    {d : ℕ} (B_param B R c ε : ℝ)
    (hB_param_nn : 0 ≤ B_param) (hBR_pos : 0 < 2 * B * R)
    (hε_pos : 0 < ε) (hεc : ε < c / 2) :
    (∫ (x : ℝ) in ε..(c/2),
        √(Real.log (coveringNumber
            (param_ball_subtype_univ_totallyBounded (d := d) B_param)
            (x / (2 * B * R))))) ≤
      (c / 2 - ε) *
        √(Real.log (coveringNumber
          (param_ball_subtype_univ_totallyBounded (d := d) B_param)
          (ε / (2 * B * R)))) := by
  classical
  set L : ℝ := 2 * B * R with hL_def
  have hL_pos : 0 < L := hBR_pos
  set hTB := param_ball_subtype_univ_totallyBounded (d := d) B_param with hTB_def
  have hε_le_half : ε ≤ c / 2 := le_of_lt hεc
  have hεL_pos : 0 < ε / L := div_pos hε_pos hL_pos
  -- Nonemptiness of the parameter-ball subtype.
  have hnonemp_param :
      (Set.univ :
        Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}).Nonempty :=
    ⟨⟨0, by simpa using hB_param_nn⟩, Set.mem_univ _⟩
  -- uIcc = Icc on [ε, c/2].
  have h_uIcc_eq : Set.uIcc ε (c / 2) = Set.Icc ε (c / 2) := by
    have : min ε (c / 2) = ε ∧ max ε (c / 2) = c / 2 := by
      refine ⟨?_, ?_⟩
      · exact min_eq_left hε_le_half
      · exact max_eq_right hε_le_half
    simp [Set.uIcc, this.1, this.2]
  -- The integrand is antitone on the interval.
  have h_antitoneOn :
      AntitoneOn (fun x : ℝ =>
        √(Real.log (coveringNumber hTB (x / L)))) (Set.uIcc ε (c / 2)) := by
    rw [h_uIcc_eq]
    have hsqrt_mono : Monotone (fun x : ℝ => √x) := fun _ _ => Real.sqrt_le_sqrt
    apply Monotone.comp_antitoneOn hsqrt_mono
    refine antitoneOn_iff_forall_lt.mpr ?_
    intro a ha b hb hab
    have ha_pos : 0 < a := lt_of_lt_of_le hε_pos ha.1
    have hb_pos : 0 < b := lt_of_lt_of_le hε_pos hb.1
    have haL_pos : 0 < a / L := div_pos ha_pos hL_pos
    have hbL_pos : 0 < b / L := div_pos hb_pos hL_pos
    have habL : a / L ≤ b / L := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hL_pos)
      exact le_of_lt hab
    apply Real.log_le_log
    · exact_mod_cast coveringNumber_nonzero hnonemp_param hTB hbL_pos
    · exact_mod_cast
        converingNumber_antitone hTB (by simp [haL_pos]) (by simp [hbL_pos]) habL
  -- Pointwise endpoint bound on Icc ε (c/2).
  have h_point :
      ∀ x ∈ Set.Icc ε (c / 2),
        √(Real.log (coveringNumber hTB (x / L))) ≤
          √(Real.log (coveringNumber hTB (ε / L))) := by
    intro x hx_mem
    have hε_in : ε ∈ Set.uIcc ε (c / 2) := by
      rw [h_uIcc_eq]; exact ⟨le_refl _, hε_le_half⟩
    have hx_in : x ∈ Set.uIcc ε (c / 2) := by
      rw [h_uIcc_eq]; exact hx_mem
    exact h_antitoneOn hε_in hx_in hx_mem.1
  -- Interval-integrability of the antitone integrand.
  have hLHS_intInt :
      IntervalIntegrable
        (fun x : ℝ => √(Real.log (coveringNumber hTB (x / L))))
        MeasureTheory.volume ε (c / 2) :=
    AntitoneOn.intervalIntegrable h_antitoneOn
  have hRHS_intInt :
      IntervalIntegrable
        (fun _ : ℝ =>
          √(Real.log (coveringNumber hTB (ε / L))))
        MeasureTheory.volume ε (c / 2) :=
    intervalIntegrable_const
  -- Apply integral_mono_on against the constant majorant.
  have hintegral_le :
      (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber hTB (x / L)))) ≤
        ∫ (_ : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber hTB (ε / L))) :=
    intervalIntegral.integral_mono_on hε_le_half hLHS_intInt hRHS_intInt h_point
  -- Constant integral = (b - a) * c.
  have hConst_int :
      (∫ (_ : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber hTB (ε / L)))) =
        (c / 2 - ε) * √(Real.log (coveringNumber hTB (ε / L))) := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  linarith [hintegral_le, hConst_int.le, hConst_int.ge]

/-- **Closed-form endpoint bound on the with-abs wide-network Dudley
integral** (Option C, with-abs analogue).

For the Dudley integrand produced by
`wide_network_rademacher_complexity_with_abs_via_dudley_paramBall`, the
integral on `[ε, c/2]` is bounded above by `(c/2 - ε)` times the
integrand at the lower endpoint `ε`. Same antitone argument as the
without-abs version; the `2 *` factor inside the log is constant so
preserves antitonicity. -/
theorem wide_network_dudley_integral_paramBall_endpoint_bound_with_abs
    {d : ℕ} (B_param B R c ε : ℝ)
    (hB_param_nn : 0 ≤ B_param) (hBR_pos : 0 < 2 * B * R)
    (hε_pos : 0 < ε) (hεc : ε < c / 2) :
    (∫ (x : ℝ) in ε..(c/2),
        √(Real.log (2 * (coveringNumber
            (param_ball_subtype_univ_totallyBounded (d := d) B_param)
            (x / (2 * B * R)) : ℝ)))) ≤
      (c / 2 - ε) *
        √(Real.log (2 * (coveringNumber
          (param_ball_subtype_univ_totallyBounded (d := d) B_param)
          (ε / (2 * B * R)) : ℝ))) := by
  classical
  set L : ℝ := 2 * B * R with hL_def
  have hL_pos : 0 < L := hBR_pos
  set hTB := param_ball_subtype_univ_totallyBounded (d := d) B_param with hTB_def
  have hε_le_half : ε ≤ c / 2 := le_of_lt hεc
  have hεL_pos : 0 < ε / L := div_pos hε_pos hL_pos
  have hnonemp_param :
      (Set.univ :
        Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}).Nonempty :=
    ⟨⟨0, by simpa using hB_param_nn⟩, Set.mem_univ _⟩
  have h_uIcc_eq : Set.uIcc ε (c / 2) = Set.Icc ε (c / 2) := by
    have : min ε (c / 2) = ε ∧ max ε (c / 2) = c / 2 := by
      refine ⟨?_, ?_⟩
      · exact min_eq_left hε_le_half
      · exact max_eq_right hε_le_half
    simp [Set.uIcc, this.1, this.2]
  -- Antitone-on for the with-abs integrand on the uIcc.
  have h_antitoneOn :
      AntitoneOn (fun x : ℝ =>
        √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ)))) (Set.uIcc ε (c / 2)) := by
    rw [h_uIcc_eq]
    have hsqrt_mono : Monotone (fun x : ℝ => √x) := fun _ _ => Real.sqrt_le_sqrt
    apply Monotone.comp_antitoneOn hsqrt_mono
    refine antitoneOn_iff_forall_lt.mpr ?_
    intro a ha b hb hab
    have ha_pos : 0 < a := lt_of_lt_of_le hε_pos ha.1
    have hb_pos : 0 < b := lt_of_lt_of_le hε_pos hb.1
    have haL_pos : 0 < a / L := div_pos ha_pos hL_pos
    have hbL_pos : 0 < b / L := div_pos hb_pos hL_pos
    have habL : a / L ≤ b / L := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hL_pos)
      exact le_of_lt hab
    have hcN_b_pos : (0 : ℝ) < (coveringNumber hTB (b / L) : ℝ) := by
      exact_mod_cast coveringNumber_nonzero hnonemp_param hTB hbL_pos
    have hcN_le : (coveringNumber hTB (b / L) : ℝ) ≤
        (coveringNumber hTB (a / L) : ℝ) := by
      exact_mod_cast
        converingNumber_antitone hTB (by simp [haL_pos]) (by simp [hbL_pos]) habL
    have h_two_b_pos : (0 : ℝ) < 2 * (coveringNumber hTB (b / L) : ℝ) := by
      positivity
    have h_two_le : 2 * (coveringNumber hTB (b / L) : ℝ) ≤
        2 * (coveringNumber hTB (a / L) : ℝ) := by linarith
    exact Real.log_le_log h_two_b_pos h_two_le
  have h_point :
      ∀ x ∈ Set.Icc ε (c / 2),
        √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ))) ≤
          √(Real.log (2 * (coveringNumber hTB (ε / L) : ℝ))) := by
    intro x hx_mem
    have hε_in : ε ∈ Set.uIcc ε (c / 2) := by
      rw [h_uIcc_eq]; exact ⟨le_refl _, hε_le_half⟩
    have hx_in : x ∈ Set.uIcc ε (c / 2) := by
      rw [h_uIcc_eq]; exact hx_mem
    exact h_antitoneOn hε_in hx_in hx_mem.1
  have hLHS_intInt :
      IntervalIntegrable
        (fun x : ℝ => √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ))))
        MeasureTheory.volume ε (c / 2) :=
    AntitoneOn.intervalIntegrable h_antitoneOn
  have hRHS_intInt :
      IntervalIntegrable
        (fun _ : ℝ =>
          √(Real.log (2 * (coveringNumber hTB (ε / L) : ℝ))))
        MeasureTheory.volume ε (c / 2) :=
    intervalIntegrable_const
  have hintegral_le :
      (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ)))) ≤
        ∫ (_ : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber hTB (ε / L) : ℝ))) :=
    intervalIntegral.integral_mono_on hε_le_half hLHS_intInt hRHS_intInt h_point
  have hConst_int :
      (∫ (_ : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber hTB (ε / L) : ℝ)))) =
        (c / 2 - ε) * √(Real.log (2 * (coveringNumber hTB (ε / L) : ℝ))) := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  linarith [hintegral_le, hConst_int.le, hConst_int.ge]

/-! ### Subtype-lift bridge: `paramBall` covering ≤ Euclidean external covering

The bridge `coveringNumber_le_externalCoveringNumber`
(`LTFP/Foundations/CoveringNumber.lean`) connects LTFP's internal
`coveringNumber` to Mathlib's `externalCoveringNumber` *on the same
space*. The endpoint Dudley integrand uses
`coveringNumber (param_ball_subtype_univ_totallyBounded B_param) δ`
(in the parameter-ball **subtype** metric), while
`covering_number_euclidean_ball` bounds
`externalCoveringNumber ε (Metric.closedBall 0 B_param)` in the
ambient `EuclideanSpace ℝ (Fin d)` metric.

To bridge them, we lift any closed-ball external cover of
`closedBall 0 B_param ⊆ EuclideanSpace ℝ (Fin d)` at radius `ε` to an
open-ball internal cover of the subtype universe at radius `4 * ε`,
preserving cardinality. The factor of `4` is composed from two
factors of `2`: one for converting closed balls to open balls (as in
the original `coveringNumber_le_externalCoveringNumber` bridge), and
one for picking subtype representatives via the triangle inequality.

This is the **honest replacement** for the dispatch sheet's
`(⌈8 √d B R B_param / ε⌉₊ + 1)^d` mental model with the factor-of-2
shift acknowledged. The final composed constant is
`(⌈16 √d B R B_param / ε⌉₊ + 1)^d` — see
`wide_network_dudley_integral_explicit_polynomial_bound` below. -/

private lemma coveringNumber_paramBall_subtype_le_externalCoveringNumber_closedBall
    {d : ℕ} {B_param : ℝ} (hB : 0 ≤ B_param)
    {ε : ℝ≥0} (hε : 0 < ε) :
    (coveringNumber (param_ball_subtype_univ_totallyBounded (d := d) B_param)
        (4 * (ε : ℝ)) : ℕ∞)
    ≤ Metric.externalCoveringNumber ε
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param) := by
  classical
  have hε_real : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have h4ε_pos : (0 : ℝ) < 4 * (ε : ℝ) := by linarith
  set hTB := param_ball_subtype_univ_totallyBounded (d := d) B_param with hTB_def
  -- Reduce to: for every external cover, LTFP.coveringNumber ≤ |C|.
  refine le_iInf₂ (fun C hC => ?_)
  by_cases hCfin : C.Finite
  · set t : Finset (EuclideanSpace ℝ (Fin d)) := hCfin.toFinset with ht_def
    -- Closed-ball-cover form of `IsCover`.
    have hC_cb : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param) ⊆
        ⋃ y ∈ C, Metric.closedBall y (ε : ℝ) := by
      have := hC.subset_iUnion_closedBall
      simpa using this
    -- Predicate: closedBall y ε intersects the parameter ball.
    set P : EuclideanSpace ℝ (Fin d) → Prop := fun y =>
      (Metric.closedBall y (ε : ℝ) ∩
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param).Nonempty
      with hP_def
    -- Lift: for each y ∈ t, pick a subtype representative from the
    -- intersection if nonempty; fall back to 0 (subtype member since
    -- B_param ≥ 0).
    set lift : EuclideanSpace ℝ (Fin d) →
        {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param} := fun y =>
      if h : P y then
        ⟨h.choose, by
          have hmem := h.choose_spec.2
          simpa [Metric.mem_closedBall, dist_zero_right] using hmem⟩
      else ⟨0, by simpa using hB⟩
      with hlift_def
    -- The lifted finset cover (in subtype).
    set t' : Finset {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param} :=
      t.image lift with ht'_def
    have ht'_card_le : t'.card ≤ t.card := Finset.card_image_le
    -- Cover property: every subtype point lies in some 4ε-open ball.
    have hCover :
        (Set.univ : Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}) ⊆
        ⋃ y ∈ t', Metric.ball y (4 * (ε : ℝ)) := by
      intro q _hq
      have hqball : q.val ∈
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param := by
        simpa [Metric.mem_closedBall, dist_zero_right] using q.property
      rcases Set.mem_iUnion₂.mp (hC_cb hqball) with ⟨y, hyC, hqy⟩
      -- P y holds with witness q.val.
      have hPy : P y := ⟨q.val, hqy, hqball⟩
      refine Set.mem_iUnion₂.mpr ⟨lift y, ?_, ?_⟩
      · have hyt : y ∈ t := hCfin.mem_toFinset.mpr hyC
        exact Finset.mem_image.mpr ⟨y, hyt, rfl⟩
      · -- dist q (lift y) < 4ε
        have hlift_val : (lift y).val = hPy.choose := by
          simp only [lift, dif_pos hPy]
        have h1 : dist q.val y ≤ (ε : ℝ) := by
          rw [Metric.mem_closedBall] at hqy
          exact hqy
        have h2 : dist hPy.choose y ≤ (ε : ℝ) := by
          have := hPy.choose_spec.1
          rw [Metric.mem_closedBall] at this
          exact this
        have hdistq : dist q (lift y) = dist q.val (lift y).val :=
          Subtype.dist_eq _ _
        rw [Metric.mem_ball, hdistq, hlift_val]
        calc dist q.val hPy.choose
            ≤ dist q.val y + dist y hPy.choose := dist_triangle _ _ _
          _ = dist q.val y + dist hPy.choose y := by rw [dist_comm y]
          _ ≤ (ε : ℝ) + (ε : ℝ) := by linarith
          _ = 2 * (ε : ℝ) := by ring
          _ < 4 * (ε : ℝ) := by linarith
    -- Witness for coveringNumber_exists at scale 4ε.
    have hwitness :
        ∃ s : Finset {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param},
          s.card = t'.card ∧
          (Set.univ : Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}) ⊆
            ⋃ y ∈ s, Metric.ball y (4 * (ε : ℝ)) :=
      ⟨t', rfl, hCover⟩
    have hfind :
        Nat.find (coveringNumber_exists hTB h4ε_pos) ≤ t'.card :=
      Nat.find_min' (coveringNumber_exists hTB h4ε_pos) hwitness
    have hLTFP_le : coveringNumber hTB (4 * (ε : ℝ)) ≤ t'.card := by
      calc coveringNumber hTB (4 * (ε : ℝ))
          = Nat.find (coveringNumber_exists hTB h4ε_pos) :=
            coveringNumber_eq hTB h4ε_pos
        _ ≤ t'.card := hfind
    have hLTFP_le_t : coveringNumber hTB (4 * (ε : ℝ)) ≤ t.card :=
      hLTFP_le.trans ht'_card_le
    have ht_card : (t.card : ℕ∞) = C.encard := by
      have h₁ : C.encard = t.card := by
        simp [ht_def, hCfin.encard_eq_coe_toFinset_card]
      exact h₁.symm
    have hcast : (coveringNumber hTB (4 * (ε : ℝ)) : ℕ∞) ≤ (t.card : ℕ∞) := by
      exact_mod_cast hLTFP_le_t
    exact hcast.trans ht_card.le
  · have hCinf : C.Infinite := hCfin
    simp [hCinf.encard_eq]

/-- **B8 N6 end-to-end explicit polynomial-rate bound.**

End-to-end composition of three pieces:
1. `covering_number_euclidean_ball` (`34db5c9`,
   `LTFP/MathlibExt/Probability/CoveringNumberEuclidean.lean`): the
   `(⌈2 √d B / δ⌉₊ + 1) ^ d` external-covering-number bound on the
   Euclidean closed ball.
2. `coveringNumber_paramBall_subtype_le_externalCoveringNumber_closedBall`
   (this file, factor-of-4 subtype-lift bridge composed from the
   open-vs-closed-ball factor of 2 from the bridge `e5d71b4` and the
   triangle-inequality factor of 2 from picking subtype reps).
3. `wide_network_dudley_integral_paramBall_endpoint_bound` (`f103f58`,
   above in this file): the endpoint Dudley integral bound
   `∫ ≤ (c/2 − ε) · √(log (coveringNumber paramBall (ε/(2BR))))`.

Composing (1) and (2) gives the cardinality bound
`coveringNumber paramBall (x/(2BR)) ≤ (⌈16 √d B R B_param / x⌉₊+1)^d`
on `ℕ`. Substituting under the `√ ∘ log` integrand (via `Real.log_pow`
to push the exponent `d` out as a multiplicative factor) and using
(3) gives:

  `∫_ε^{c/2} √(log (coveringNumber paramBall (x/(2BR)))) dx
    ≤ (c/2 − ε) · √(d · log (⌈16 √d B R B_param / ε⌉₊ + 1))`

This is the explicit O((BR · B_param / ε)^{d/2} · (c/2 − ε))-style
polynomial-rate bound for the B8 N6 wide-network Rademacher complexity
Dudley integral.

**Constant deviation from dispatch sheet:** the dispatch sheet's mental
model expected the leading constant inside the ceiling to be `8` (one
factor of 2 from the bridge `e5d71b4`). The honest constant is `16`:
the bridge applies between `coveringNumber` and `externalCoveringNumber`
*on the same space*, and to connect the parameter-ball subtype's
internal covering number to the ambient Euclidean closed ball's
external covering number requires an additional factor of 2 from
picking subtype representatives via the triangle inequality
(`closedBall y ε ⊆ closedBall y' (2 ε)` when `y'` is the nearest
subtype point to `y`). Total constant: `4 · 2 · 2 = 16`. -/
theorem wide_network_dudley_integral_explicit_polynomial_bound
    {d : ℕ} (B_param B R c ε : ℝ)
    (hd : 1 ≤ d)
    (hB_param_nn : 0 ≤ B_param) (hBR_pos : 0 < 2 * B * R)
    (hε_pos : 0 < ε) (hεc : ε < c / 2) :
    (∫ (x : ℝ) in ε..(c/2),
        √(Real.log (coveringNumber
            (param_ball_subtype_univ_totallyBounded (d := d) B_param)
            (x / (2 * B * R))))) ≤
      (c / 2 - ε) *
        √((d : ℝ) *
          Real.log ((⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1 : ℕ) : ℝ)) := by
  classical
  set L : ℝ := 2 * B * R with hL_def
  have hL_pos : 0 < L := hBR_pos
  set hTB := param_ball_subtype_univ_totallyBounded (d := d) B_param with hTB_def
  have hε_le_half : ε ≤ c / 2 := le_of_lt hεc
  have h_half_minus_ε_nn : 0 ≤ c / 2 - ε := by linarith
  have hεL_pos : 0 < ε / L := div_pos hε_pos hL_pos
  -- Nonemptiness of the parameter-ball subtype.
  have hnonemp_param :
      (Set.univ :
        Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}).Nonempty :=
    ⟨⟨0, by simpa using hB_param_nn⟩, Set.mem_univ _⟩
  -- Step 1: apply the f103f58 endpoint bound.
  have h_endpoint :=
    wide_network_dudley_integral_paramBall_endpoint_bound (d := d)
      B_param B R c ε hB_param_nn hBR_pos hε_pos hεc
  -- Step 2: bound the endpoint integrand by the explicit polynomial.
  -- Let δ := ε / L (the scale at the lower endpoint). Pick η : ℝ≥0
  -- such that 4 * η = δ, i.e., η = δ / 4 = ε / (8 * B * R).
  set δ : ℝ := ε / L with hδ_def
  have hδ_pos : 0 < δ := hεL_pos
  set η_real : ℝ := δ / 4 with hη_real_def
  have hη_real_pos : 0 < η_real := by
    show 0 < δ / 4
    positivity
  set η : ℝ≥0 := ⟨η_real, hη_real_pos.le⟩ with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def, ← NNReal.coe_pos]; exact hη_real_pos
  have hη_ne : η ≠ 0 := ne_of_gt hη_pos
  have hη_coe : (η : ℝ) = η_real := rfl
  have h4η_eq : 4 * (η : ℝ) = δ := by
    rw [hη_coe, hη_real_def]; ring
  -- Apply the subtype-lift bridge:
  -- `coveringNumber paramBall δ ≤ externalCoveringNumber η (closedBall 0 B_param)`.
  have h_bridge :
      (coveringNumber hTB δ : ℕ∞)
        ≤ Metric.externalCoveringNumber η
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param) := by
    have h := coveringNumber_paramBall_subtype_le_externalCoveringNumber_closedBall
      (d := d) (B_param := B_param) hB_param_nn hη_pos
    rwa [h4η_eq] at h
  -- Apply the Euclidean ball external cover bound.
  have h_euclid :
      Metric.externalCoveringNumber η
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param) ≤
        ((⌈2 * Real.sqrt d * B_param / (η : ℝ)⌉₊ + 1 : ℕ) ^ d : ℕ) :=
    covering_number_euclidean_ball d B_param η hd hB_param_nn hη_ne
  -- Identify the ceiling argument:
  -- 2 * √d * B_param / η = 2 * √d * B_param * (8 * B * R / ε) = 16 √d B R B_param / ε.
  have h_ratio_eq :
      2 * Real.sqrt d * B_param / (η : ℝ) = 16 * Real.sqrt d * B * R * B_param / ε := by
    rw [hη_coe, hη_real_def, hδ_def, hL_def]
    have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
    have hBR_ne : 2 * B * R ≠ 0 := ne_of_gt hBR_pos
    field_simp
    ring
  -- Set the explicit count N := (⌈16 √d B R B_param / ε⌉₊ + 1)^d.
  set N : ℕ := (⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1) ^ d with hN_def
  have h_euclid_N :
      Metric.externalCoveringNumber η
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param) ≤
        (N : ℕ∞) := by
    have := h_euclid
    rw [h_ratio_eq] at this
    exact_mod_cast this
  -- Combine bridge + Euclidean: `coveringNumber paramBall δ ≤ N` in ℕ.
  have h_cn_le : (coveringNumber hTB δ : ℕ∞) ≤ (N : ℕ∞) :=
    h_bridge.trans h_euclid_N
  have h_cn_le_nat : coveringNumber hTB δ ≤ N := by
    exact_mod_cast h_cn_le
  -- Cast to ℝ.
  have h_cn_le_real :
      (coveringNumber hTB δ : ℝ) ≤ (N : ℝ) := by exact_mod_cast h_cn_le_nat
  -- Bound log: log(coveringNumber) ≤ log(N) = d * log(⌈...⌉ + 1).
  have h_cn_pos_real : (0 : ℝ) < (coveringNumber hTB δ : ℝ) := by
    exact_mod_cast coveringNumber_nonzero hnonemp_param hTB hδ_pos
  have h_log_le_N :
      Real.log (coveringNumber hTB δ : ℝ) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log h_cn_pos_real h_cn_le_real
  -- Rewrite log(N) = d * log(⌈...⌉ + 1).
  set K : ℕ := ⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1 with hK_def
  have hN_eq : N = K ^ d := by rw [hN_def, hK_def]
  have h_log_N_eq :
      Real.log (N : ℝ) = (d : ℝ) * Real.log (K : ℝ) := by
    rw [hN_eq]
    push_cast
    exact Real.log_pow (K : ℝ) d
  have h_K_pos_real : (0 : ℝ) < (K : ℝ) := by
    have hK_pos : 0 < K := by
      rw [hK_def]; exact Nat.succ_pos _
    exact_mod_cast hK_pos
  have h_K_ge_one : (1 : ℝ) ≤ (K : ℝ) := by
    have : 1 ≤ K := by rw [hK_def]; exact Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast this
  -- log(K) ≥ 0.
  have h_logK_nn : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg h_K_ge_one
  have h_d_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have h_d_logK_nn : 0 ≤ (d : ℝ) * Real.log (K : ℝ) :=
    mul_nonneg h_d_nn h_logK_nn
  -- √(log (coveringNumber)) ≤ √(d * log K).
  have h_sqrt_le :
      Real.sqrt (Real.log (coveringNumber hTB δ : ℝ)) ≤
        Real.sqrt ((d : ℝ) * Real.log (K : ℝ)) := by
    apply Real.sqrt_le_sqrt
    rw [← h_log_N_eq]
    exact h_log_le_N
  -- Multiply both sides by `(c/2 - ε) ≥ 0`.
  have h_rhs_le :
      (c / 2 - ε) *
        Real.sqrt (Real.log (coveringNumber hTB δ : ℝ)) ≤
      (c / 2 - ε) * Real.sqrt ((d : ℝ) * Real.log (K : ℝ)) := by
    exact mul_le_mul_of_nonneg_left h_sqrt_le h_half_minus_ε_nn
  -- Chain with the endpoint bound.
  calc (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber hTB (x / L))))
      ≤ (c / 2 - ε) *
          √(Real.log (coveringNumber hTB (ε / L))) := h_endpoint
    _ = (c / 2 - ε) *
          √(Real.log (coveringNumber hTB δ : ℝ)) := by
        rw [hδ_def]
    _ ≤ (c / 2 - ε) *
          √((d : ℝ) * Real.log (K : ℝ)) := h_rhs_le
    _ = (c / 2 - ε) *
          √((d : ℝ) *
            Real.log ((⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1 : ℕ) : ℝ)) := by
        rw [hK_def]

/-! ### End-to-end abstract i.i.d. × explicit polynomial-rate bound

Composes `wide_network_expected_two_rademacher_le_dudley_paramBall_of_ae`
(the abstract i.i.d.-measure lift) with
`wide_network_dudley_integral_explicit_polynomial_bound` (the explicit
polynomial-rate Dudley bound) to give a fully-closed-form
measure-theoretic expected-rate bound on the wide-network Rademacher
complexity. The RHS depends only on `(B_param, R, B, d, ε, m, c)` and
is measure-independent. -/

/-- **End-to-end abstract i.i.d. × explicit polynomial-rate bound.**

Under the hypotheses that the i.i.d. sample measure `ν` a.s. satisfies
the wide-network bounded-support / parameter-ball / empirical-norm
assumptions, the expected scaled Rademacher complexity
`∫ 2 · R̂_m ∂ν` is bounded by the closed-form polynomial rate

  `2 · (4 ε + (12 / √m) · (c/2 − ε) · √(d · log(⌈16 √d B R B_param / ε⌉₊ + 1)))`.

The RHS is a constant in `(B_param, R, B, d, ε, m, c)` and does *not*
depend on the measure `ν` — the integral against `ν` collapses to a
pointwise bound by the deterministic polynomial rate.

This is the composition of
`wide_network_expected_two_rademacher_le_dudley_paramBall_of_ae`
(`5f861d9`, abstract i.i.d. lift) with
`wide_network_dudley_integral_explicit_polynomial_bound`
(`1bce222`, explicit polynomial Dudley bound). -/
theorem wide_network_expected_two_rademacher_le_explicit_polynomial_paramBall
    {d m : ℕ}
    (ν : MeasureTheory.Measure (Fin m → EuclideanSpace ℝ (Fin d) × ℝ))
    [MeasureTheory.IsProbabilityMeasure ν]
    (B_param R B c ε : ℝ)
    (hd : 1 ≤ d)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B) (hB_param_nn : 0 ≤ B_param)
    (hBR_pos : 0 < 2 * B * R)
    (hε_pos : 0 < ε) (hm_pos : 0 < m) (hεc : ε < c / 2)
    (hae :
      ∀ᵐ (S : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) ∂ν,
        (∀ i, ‖(S i).1‖ ≤ R) ∧
        (∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
          ∀ i, |@inner ℝ _ _ θ (S i).1 - (S i).2| ≤ B) ∧
        (∀ θ : {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param},
          empiricalNorm (linearizedRiskSample (fun i => (S i).1) (fun i => (S i).2))
            (linearizedRiskFamily (d := d) B_param θ) ≤ c))
    (hint : MeasureTheory.Integrable
      (fun S : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        2 * empiricalRademacherComplexity_without_abs m
              (linearizedRiskFamily (d := d) B_param) S) ν) :
    ∫ S, 2 * empiricalRademacherComplexity_without_abs m
            (linearizedRiskFamily (d := d) B_param) S ∂ν ≤
      2 * (4 * ε + (12 / Real.sqrt m) *
        ((c / 2 - ε) *
          √((d : ℝ) *
            Real.log ((⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1 : ℕ) : ℝ)))) := by
  -- Step 1: apply the abstract i.i.d. lift (5f861d9).
  have h_iid :=
    wide_network_expected_two_rademacher_le_dudley_paramBall_of_ae
      (d := d) (m := m) ν B_param R B c ε
      hR_nn hB_nn hB_param_nn hBR_pos hε_pos hm_pos hεc hae hint
  -- Step 2: apply the explicit polynomial-rate Dudley bound (1bce222).
  have h_poly :=
    wide_network_dudley_integral_explicit_polynomial_bound
      (d := d) B_param B R c ε hd hB_param_nn hBR_pos hε_pos hεc
  -- Step 3: chain via monotonicity. We need:
  --   12 / √m ≥ 0 and 2 ≥ 0 for the outer multipliers.
  have h_sqrt_m_nn : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have h_factor_nn : 0 ≤ 12 / Real.sqrt m := by positivity
  -- Multiply h_poly by (12 / √m).
  have h_scaled :
      (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (coveringNumber
              (param_ball_subtype_univ_totallyBounded (d := d) B_param)
              (x / (2 * B * R))))) ≤
        (12 / Real.sqrt m) *
          ((c / 2 - ε) *
            √((d : ℝ) *
              Real.log ((⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1 : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_left h_poly h_factor_nn
  -- Add 4*ε.
  have h_add :
      4 * ε +
        (12 / Real.sqrt m) *
          (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (coveringNumber
                (param_ball_subtype_univ_totallyBounded (d := d) B_param)
                (x / (2 * B * R))))) ≤
      4 * ε +
        (12 / Real.sqrt m) *
          ((c / 2 - ε) *
            √((d : ℝ) *
              Real.log ((⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1 : ℕ) : ℝ))) :=
    by linarith
  -- Multiply by 2.
  have h_outer :
      2 * (4 * ε +
        (12 / Real.sqrt m) *
          (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (coveringNumber
                (param_ball_subtype_univ_totallyBounded (d := d) B_param)
                (x / (2 * B * R)))))) ≤
      2 * (4 * ε +
        (12 / Real.sqrt m) *
          ((c / 2 - ε) *
            √((d : ℝ) *
              Real.log ((⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1 : ℕ) : ℝ)))) :=
    mul_le_mul_of_nonneg_left h_add (by norm_num)
  exact h_iid.trans h_outer

/-! ### With-abs i.i.d. × explicit polynomial-rate bound

The with-abs analogues of
`wide_network_expected_two_rademacher_le_dudley_paramBall_of_ae`
(`5f861d9`, the abstract i.i.d. lift) and
`wide_network_expected_two_rademacher_le_explicit_polynomial_paramBall`
(`cb6fb3f`, the end-to-end polynomial-rate composition).

The without-abs side's per-sample bound is via
`wide_network_two_rademacher_complexity_via_dudley_paramBall` whose RHS
contains `√(log(coveringNumber ...))`. The with-abs side's per-sample
bound (`wide_network_rademacher_complexity_with_abs_via_dudley_paramBall`,
`ac3a269`) contains `√(log(2 · coveringNumber ...))` — the factor `2`
inside the log is the negation-closure correction from
`dudley_entropy_integral_bound_with_abs`. Apart from that and the
absence of the symmetrisation leading `2 *`, the proof shape is the
same: integrate the deterministic per-sample bound against a `ν`-a.e.
bundle of the wide-network hypotheses, then bound the Dudley integral
endpoint by the explicit polynomial form.

For the polynomial-rate step, we use `log(2 · N) = log 2 + log N`
under positivity, then bound `log N ≤ d · log K` via the same
external-covering bridge used by `1bce222`. This gives the closed
form

  `(c/2 - ε) · √(log 2 + d · log K)`

with `K = ⌈16 √d B R B_param / ε⌉₊ + 1`, matching the without-abs
form up to the additive `log 2` inside the square root. -/

/-- **With-abs abstract i.i.d. lift.**

The with-abs analogue of
`wide_network_expected_two_rademacher_le_dudley_paramBall_of_ae`
(`5f861d9`), composing the i.i.d.-measure a.e. bundle of wide-network
hypotheses with
`wide_network_rademacher_complexity_with_abs_via_dudley_paramBall`
(`ac3a269`) instead of the without-abs deterministic bound.

The RHS matches the with-abs Dudley integrand `log(2 · coveringNumber)`
and has no leading `2 *` factor (the LHS is the *with-abs*
`empiricalRademacherComplexity`, which absorbs absolute values into
the supremum directly). -/
theorem wide_network_expected_rademacher_with_abs_le_dudley_paramBall_of_ae
    {d m : ℕ}
    (ν : MeasureTheory.Measure (Fin m → EuclideanSpace ℝ (Fin d) × ℝ))
    [MeasureTheory.IsProbabilityMeasure ν]
    (B_param R B c ε : ℝ)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B) (hB_param_nn : 0 ≤ B_param)
    (hBR_pos : 0 < 2 * B * R)
    (hε_pos : 0 < ε) (hm_pos : 0 < m) (hεc : ε < c / 2)
    (hae :
      ∀ᵐ (S : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) ∂ν,
        (∀ i, ‖(S i).1‖ ≤ R) ∧
        (∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
          ∀ i, |@inner ℝ _ _ θ (S i).1 - (S i).2| ≤ B) ∧
        (∀ θ : {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param},
          empiricalNorm (linearizedRiskSample (fun i => (S i).1) (fun i => (S i).2))
            (linearizedRiskFamily (d := d) B_param θ) ≤ c))
    (hint : MeasureTheory.Integrable
      (fun S : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        empiricalRademacherComplexity m
              (linearizedRiskFamily (d := d) B_param) S) ν) :
    ∫ S, empiricalRademacherComplexity m
            (linearizedRiskFamily (d := d) B_param) S ∂ν ≤
      (4 * ε + (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber
              (param_ball_subtype_univ_totallyBounded (d := d) B_param)
              (x / (2 * B * R)) : ℝ))))) := by
  classical
  -- Abbreviation for the deterministic with-abs Dudley RHS (sample-independent).
  set DudleyRHS : ℝ :=
    (4 * ε + (12 / Real.sqrt m) *
      (∫ (x : ℝ) in ε..(c/2),
        √(Real.log (2 * (coveringNumber
            (param_ball_subtype_univ_totallyBounded (d := d) B_param)
            (x / (2 * B * R)) : ℝ))))) with hDudleyRHS_def
  -- Pointwise a.e. bound: for ν-a.e. S, the deterministic with-abs theorem applies.
  have hae_bound :
      (fun S : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
          empiricalRademacherComplexity m
                (linearizedRiskFamily (d := d) B_param) S)
        ≤ᵐ[ν] (fun _ => DudleyRHS) := by
    filter_upwards [hae] with S hS
    obtain ⟨hx_S, hbound_S, hcs_S⟩ := hS
    -- Reconstruct xs, ys from S and apply the deterministic theorem.
    set xs : Fin m → EuclideanSpace ℝ (Fin d) := fun i => (S i).1 with hxs_def
    set ys : Fin m → ℝ := fun i => (S i).2 with hys_def
    have hS_eq : S = linearizedRiskSample xs ys := by
      funext i
      simp [linearizedRiskSample, xs, ys]
    have hbase :=
      wide_network_rademacher_complexity_with_abs_via_dudley_paramBall
        (d := d) (m := m) xs ys B_param R B c ε
        hR_nn hB_nn hB_param_nn hBR_pos hε_pos hm_pos hεc
        hx_S hbound_S hcs_S
    rw [hS_eq]
    exact hbase
  -- Integrate.
  have hConst_int : MeasureTheory.Integrable
      (fun _ : Fin m → EuclideanSpace ℝ (Fin d) × ℝ => DudleyRHS) ν :=
    MeasureTheory.integrable_const _
  have hstep1 :
      ∫ S, empiricalRademacherComplexity m
              (linearizedRiskFamily (d := d) B_param) S ∂ν ≤
      ∫ _ : Fin m → EuclideanSpace ℝ (Fin d) × ℝ, DudleyRHS ∂ν :=
    MeasureTheory.integral_mono_ae hint hConst_int hae_bound
  have hstep2 : ∫ _ : Fin m → EuclideanSpace ℝ (Fin d) × ℝ, DudleyRHS ∂ν = DudleyRHS := by
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ]
    simp
  linarith [hstep1, hstep2.le, hstep2.ge]

/-- **With-abs end-to-end abstract i.i.d. × explicit polynomial-rate
bound.**

The with-abs analogue of
`wide_network_expected_two_rademacher_le_explicit_polynomial_paramBall`
(`cb6fb3f`). Composes the with-abs i.i.d. lift above with the explicit
Euclidean-cover cardinality bound to give a closed-form
measure-theoretic expected-rate bound on the with-abs Rademacher
complexity.

Compared to the without-abs side at `cb6fb3f`, the integrand has
`log(2 · coveringNumber)` instead of `log(coveringNumber)`, so the
final rate has an additive `log 2` inside the square root:

  `4 ε + (12 / √m) · (c/2 − ε) · √(log 2 + d · log K)`

with `K = ⌈16 √d B R B_param / ε⌉₊ + 1`. The proof composes the
with-abs i.i.d. lift, the with-abs endpoint bound (`5dcd80f`-analogue,
already in this file), and the same external-covering bridge used by
`1bce222`. -/
theorem wide_network_expected_rademacher_with_abs_le_explicit_polynomial_paramBall
    {d m : ℕ}
    (ν : MeasureTheory.Measure (Fin m → EuclideanSpace ℝ (Fin d) × ℝ))
    [MeasureTheory.IsProbabilityMeasure ν]
    (B_param R B c ε : ℝ)
    (hd : 1 ≤ d)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B) (hB_param_nn : 0 ≤ B_param)
    (hBR_pos : 0 < 2 * B * R)
    (hε_pos : 0 < ε) (hm_pos : 0 < m) (hεc : ε < c / 2)
    (hae :
      ∀ᵐ (S : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) ∂ν,
        (∀ i, ‖(S i).1‖ ≤ R) ∧
        (∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B_param →
          ∀ i, |@inner ℝ _ _ θ (S i).1 - (S i).2| ≤ B) ∧
        (∀ θ : {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param},
          empiricalNorm (linearizedRiskSample (fun i => (S i).1) (fun i => (S i).2))
            (linearizedRiskFamily (d := d) B_param θ) ≤ c))
    (hint : MeasureTheory.Integrable
      (fun S : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        empiricalRademacherComplexity m
              (linearizedRiskFamily (d := d) B_param) S) ν) :
    ∫ S, empiricalRademacherComplexity m
            (linearizedRiskFamily (d := d) B_param) S ∂ν ≤
      (4 * ε + (12 / Real.sqrt m) *
        ((c / 2 - ε) *
          √(Real.log 2 +
            (d : ℝ) *
              Real.log ((⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1 : ℕ) : ℝ)))) := by
  classical
  -- Step 1: apply the with-abs i.i.d. lift.
  have h_iid :=
    wide_network_expected_rademacher_with_abs_le_dudley_paramBall_of_ae
      (d := d) (m := m) ν B_param R B c ε
      hR_nn hB_nn hB_param_nn hBR_pos hε_pos hm_pos hεc hae hint
  -- Step 2: bound the with-abs Dudley integral by the explicit polynomial form.
  -- We reproduce the chain from `1bce222` but for the `log(2 · ·)` integrand.
  set L : ℝ := 2 * B * R with hL_def
  have hL_pos : 0 < L := hBR_pos
  set hTB := param_ball_subtype_univ_totallyBounded (d := d) B_param with hTB_def
  have hε_le_half : ε ≤ c / 2 := le_of_lt hεc
  have h_half_minus_ε_nn : 0 ≤ c / 2 - ε := by linarith
  have hεL_pos : 0 < ε / L := div_pos hε_pos hL_pos
  -- Nonemptiness of the parameter-ball subtype.
  have hnonemp_param :
      (Set.univ :
        Set {θ : EuclideanSpace ℝ (Fin d) // ‖θ‖ ≤ B_param}).Nonempty :=
    ⟨⟨0, by simpa using hB_param_nn⟩, Set.mem_univ _⟩
  -- Step 2a: with-abs endpoint bound.
  have h_endpoint :=
    wide_network_dudley_integral_paramBall_endpoint_bound_with_abs (d := d)
      B_param B R c ε hB_param_nn hBR_pos hε_pos hεc
  -- Step 2b: bound the endpoint integrand `log(2 · N(ε/L))` by `log 2 + d · log K`.
  -- Replicate the bridge chain from `1bce222`.
  set δ : ℝ := ε / L with hδ_def
  have hδ_pos : 0 < δ := hεL_pos
  set η_real : ℝ := δ / 4 with hη_real_def
  have hη_real_pos : 0 < η_real := by
    show 0 < δ / 4
    positivity
  set η : ℝ≥0 := ⟨η_real, hη_real_pos.le⟩ with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def, ← NNReal.coe_pos]; exact hη_real_pos
  have hη_ne : η ≠ 0 := ne_of_gt hη_pos
  have hη_coe : (η : ℝ) = η_real := rfl
  have h4η_eq : 4 * (η : ℝ) = δ := by
    rw [hη_coe, hη_real_def]; ring
  -- Subtype-lift bridge.
  have h_bridge :
      (coveringNumber hTB δ : ℕ∞)
        ≤ Metric.externalCoveringNumber η
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param) := by
    have h := coveringNumber_paramBall_subtype_le_externalCoveringNumber_closedBall
      (d := d) (B_param := B_param) hB_param_nn hη_pos
    rwa [h4η_eq] at h
  -- Euclidean ball external cover bound.
  have h_euclid :
      Metric.externalCoveringNumber η
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param) ≤
        ((⌈2 * Real.sqrt d * B_param / (η : ℝ)⌉₊ + 1 : ℕ) ^ d : ℕ) :=
    covering_number_euclidean_ball d B_param η hd hB_param_nn hη_ne
  -- Identify ceiling argument.
  have h_ratio_eq :
      2 * Real.sqrt d * B_param / (η : ℝ) = 16 * Real.sqrt d * B * R * B_param / ε := by
    rw [hη_coe, hη_real_def, hδ_def, hL_def]
    have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
    have hBR_ne : 2 * B * R ≠ 0 := ne_of_gt hBR_pos
    field_simp
    ring
  set N : ℕ := (⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1) ^ d with hN_def
  have h_euclid_N :
      Metric.externalCoveringNumber η
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B_param) ≤
        (N : ℕ∞) := by
    have := h_euclid
    rw [h_ratio_eq] at this
    exact_mod_cast this
  have h_cn_le : (coveringNumber hTB δ : ℕ∞) ≤ (N : ℕ∞) :=
    h_bridge.trans h_euclid_N
  have h_cn_le_nat : coveringNumber hTB δ ≤ N := by
    exact_mod_cast h_cn_le
  have h_cn_le_real :
      (coveringNumber hTB δ : ℝ) ≤ (N : ℝ) := by exact_mod_cast h_cn_le_nat
  -- Positivity of the covering number.
  have h_cn_pos_real : (0 : ℝ) < (coveringNumber hTB δ : ℝ) := by
    exact_mod_cast coveringNumber_nonzero hnonemp_param hTB hδ_pos
  -- 2 * N > 0.
  have h_2N_pos : (0 : ℝ) < 2 * (coveringNumber hTB δ : ℝ) := by positivity
  -- 2 * coveringNumber ≤ 2 * N.
  have h_2cn_le : 2 * (coveringNumber hTB δ : ℝ) ≤ 2 * (N : ℝ) := by linarith
  -- Identify K.
  set K : ℕ := ⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1 with hK_def
  have hN_eq : N = K ^ d := by rw [hN_def, hK_def]
  have h_K_pos_real : (0 : ℝ) < (K : ℝ) := by
    have hK_pos : 0 < K := by
      rw [hK_def]; exact Nat.succ_pos _
    exact_mod_cast hK_pos
  have h_K_ge_one : (1 : ℝ) ≤ (K : ℝ) := by
    have : 1 ≤ K := by rw [hK_def]; exact Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast this
  have h_logK_nn : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg h_K_ge_one
  have h_d_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have h_d_logK_nn : 0 ≤ (d : ℝ) * Real.log (K : ℝ) := mul_nonneg h_d_nn h_logK_nn
  -- log(2 * coveringNumber) ≤ log(2 * N) = log 2 + log N = log 2 + d * log K.
  have h_2N_real_pos : (0 : ℝ) < 2 * (N : ℝ) := by
    have hN_real_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le h_cn_pos_real h_cn_le_real
    linarith
  have h_log_2cn_le :
      Real.log (2 * (coveringNumber hTB δ : ℝ)) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log h_2N_pos h_2cn_le
  have h_log_2N_eq :
      Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) := by
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    have hN_real_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le h_cn_pos_real h_cn_le_real
    exact Real.log_mul (ne_of_gt h2_pos) (ne_of_gt hN_real_pos)
  have h_log_N_eq :
      Real.log (N : ℝ) = (d : ℝ) * Real.log (K : ℝ) := by
    rw [hN_eq]
    push_cast
    exact Real.log_pow (K : ℝ) d
  have h_log_2cn_bound :
      Real.log (2 * (coveringNumber hTB δ : ℝ)) ≤
        Real.log 2 + (d : ℝ) * Real.log (K : ℝ) := by
    calc Real.log (2 * (coveringNumber hTB δ : ℝ))
        ≤ Real.log (2 * (N : ℝ)) := h_log_2cn_le
      _ = Real.log 2 + Real.log (N : ℝ) := h_log_2N_eq
      _ = Real.log 2 + (d : ℝ) * Real.log (K : ℝ) := by rw [h_log_N_eq]
  -- √(log(2 · coveringNumber)) ≤ √(log 2 + d · log K).
  have h_sqrt_le :
      Real.sqrt (Real.log (2 * (coveringNumber hTB δ : ℝ))) ≤
        Real.sqrt (Real.log 2 + (d : ℝ) * Real.log (K : ℝ)) :=
    Real.sqrt_le_sqrt h_log_2cn_bound
  -- Multiply by (c/2 - ε) ≥ 0.
  have h_endpoint_le_poly :
      (c / 2 - ε) *
        √(Real.log (2 * (coveringNumber hTB δ : ℝ))) ≤
      (c / 2 - ε) *
        √(Real.log 2 + (d : ℝ) * Real.log (K : ℝ)) :=
    mul_le_mul_of_nonneg_left h_sqrt_le h_half_minus_ε_nn
  -- Chain endpoint + polynomial bound.
  have h_integral_le :
      (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ)))) ≤
        (c / 2 - ε) *
          √(Real.log 2 + (d : ℝ) * Real.log (K : ℝ)) := by
    calc (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ))))
        ≤ (c / 2 - ε) *
            √(Real.log (2 * (coveringNumber hTB (ε / L) : ℝ))) := h_endpoint
      _ = (c / 2 - ε) *
            √(Real.log (2 * (coveringNumber hTB δ : ℝ))) := by rw [hδ_def]
      _ ≤ (c / 2 - ε) *
            √(Real.log 2 + (d : ℝ) * Real.log (K : ℝ)) := h_endpoint_le_poly
  -- Step 3: chain via monotonicity.
  have h_factor_nn : 0 ≤ 12 / Real.sqrt m := by positivity
  have h_scaled :
      (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c/2),
          √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ)))) ≤
        (12 / Real.sqrt m) *
          ((c / 2 - ε) *
            √(Real.log 2 + (d : ℝ) * Real.log (K : ℝ))) :=
    mul_le_mul_of_nonneg_left h_integral_le h_factor_nn
  have h_add :
      (4 * ε +
        (12 / Real.sqrt m) *
          (∫ (x : ℝ) in ε..(c/2),
            √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ))))) ≤
      (4 * ε +
        (12 / Real.sqrt m) *
          ((c / 2 - ε) *
            √(Real.log 2 + (d : ℝ) * Real.log (K : ℝ)))) := by linarith
  -- Unfold L and K to match the headline form, then chain with h_iid.
  -- h_iid has the same LHS and matches our intermediate via `L = 2*B*R`.
  have h_iid' :
      ∫ S, empiricalRademacherComplexity m
              (linearizedRiskFamily (d := d) B_param) S ∂ν ≤
        (4 * ε +
          (12 / Real.sqrt m) *
            (∫ (x : ℝ) in ε..(c/2),
              √(Real.log (2 * (coveringNumber hTB (x / L) : ℝ))))) := by
    -- L = 2 * B * R and hTB unfolds matter only for definitional equality.
    show _ ≤ _
    convert h_iid using 0
  have h_final :
      (4 * ε +
        (12 / Real.sqrt m) *
          ((c / 2 - ε) *
            √(Real.log 2 + (d : ℝ) * Real.log (K : ℝ)))) =
      (4 * ε +
        (12 / Real.sqrt m) *
          ((c / 2 - ε) *
            √(Real.log 2 +
              (d : ℝ) *
                Real.log
                  ((⌈16 * Real.sqrt d * B * R * B_param / ε⌉₊ + 1 : ℕ) : ℝ)))) := by
    rw [hK_def]
  linarith [h_iid'.trans (h_add.trans h_final.le)]

end ClosureViaDudley

end LTFP
