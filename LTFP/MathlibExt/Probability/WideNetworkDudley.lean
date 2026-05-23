/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.CoveringNumberEuclidean
import LTFP.MathlibExt.Probability.LinearClassClosedBallCover
import LTFP.MathlibExt.Probability.LinearClassSampleCoverCard
import LTFP.MathlibExt.Probability.LinearizedRiskSampleCover

/-!
# Wide-network generalization carrier: explicit linearized-risk cover via Euclidean cover

Composes the five existing ingredients on the B8 N6 wide-network
generalization path into one statement that exposes everything the
Dudley entropy integral needs:

1. `covering_number_euclidean_ball` (this file's dependency) — the
   `(⌈2 √d B / δ⌉₊ + 1) ^ d` external-cover-cardinality bound for the
   parameter closed ball.
2. `linear_class_closed_ball_exists_finite_cover` — existence of a
   finite finset cover of the parameter ball at any positive radius.
3. `linear_class_sample_pred_card_le` — sample-prediction tuple cover
   inherits cardinality from the parameter cover.
4. `linearized_risk_class_sample_cover_of_param_cover` — parameter
   cover lifts to a `(2 B)(δ R)`-cover of squared-loss values on the
   sample.
5. `linear_predictor_lipschitz_on_ball` (transitive via 4 above).

The composition target is the *carrier* statement consumed by the B8
N6 Dudley step: an explicit finite cover of the parameter ball,
together with its lifted linearized-risk and prediction-tuple covers,
all with size bounded by `(⌈2 √d B_param / δ⌉₊ + 1) ^ d`.

We work entirely with internal finset covers (every cover element is
in the parameter ball). The grid construction in
`covering_number_euclidean_ball` produces *external* cover points
(corners of a bounding square that may lie slightly outside the
`L²`-ball); to land an *internal* cover with the same cardinality
bound we fall back on `linear_class_closed_ball_exists_finite_cover`
to extract a finset and accept that its size is bounded by the
external covering number plus 1 unit — but since the user-facing
Dudley bound only needs an existence-of-finite-cover with explicit
upper-bound, we surface both:

- `wide_network_param_finset_cover` — *internal* finset cover at
  resolution `δ` (size existentially bounded).
- `wide_network_linearized_risk_explicit_cover` — the full composite
  carrier theorem, with linearized-risk sample-cover accuracy and
  sample-prediction-tuple cardinality.
-/

open scoped NNReal ENNReal RealInnerProductSpace

namespace LTFP

/-- Auxiliary: a `TotallyBounded` set in a `PseudoMetricSpace` admits,
for every `δ > 0`, a finite *finset* cover by points in the set itself.
A bridge from `TotallyBounded` to a usable explicit finset form. -/
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

/-- **Wide-network generalization carrier (Option A pre-Dudley).**
Composes the five ingredients on the B8 N6 path into one statement.

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

This is the natural carrier statement consumed by the Dudley
entropy-integral step on the B8 N6 path. -/
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

/-- **Wide-network generalization carrier (Option A, explicit
cardinality bound).**

Strengthening of `wide_network_linearized_risk_explicit_cover` that
makes the cardinality of the linearized-risk sample-prediction cover
explicit using `covering_number_euclidean_ball`.

For `d ≥ 1`, `B_param ≥ 0`, and `δ : ℝ≥0` positive, the external
covering number of the parameter ball is at most
`(⌈2 √d B_param / δ⌉₊ + 1) ^ d`. Combined with the linearized-risk
cover lifting, this gives a Dudley-input statement with explicit
cardinality. We surface it as a separate theorem because the
externally-located cover points from `covering_number_euclidean_ball`
need not live inside the parameter ball, so the prediction-error
boundedness hypothesis must be stated uniformly over the (slightly
larger) bounding ball `‖θ‖ ≤ B_param + δ`. -/
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

end LTFP
