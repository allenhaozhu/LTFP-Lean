/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import LTFP.MathlibExt.Probability.RandomFeatureDynamics
import LTFP.MathlibExt.Probability.WideNetworkDudley

/-!
# Random-feature exact-linearization tail bound
(B8 N5 random-feature carrier)

For the output-layer-only random-feature model, the first-order
Taylor expansion of the prediction map at any base point is *exact*
— there is no nonlinear remainder in the output-layer parameter `a`.
This file packages that algebraic fact into a probabilistic tail
bound: the event that the linearization error is positive somewhere
is empty, hence has measure zero, and is therefore bounded by any
non-negative slack `δ`.

## What this file is — and what it is NOT

This file closes the **random-feature exact-linearization tail bound**
only. It is the cleanest possible "lazy training" statement in the
output-layer-only random-feature parametrization, where linearity in
`a` makes the bound trivial (the bad event is *empty*, not merely
small).

Per the honesty note attached to `RandomFeatureDynamics.lean`:

> This closes output-layer-only random-feature prediction. It does
> NOT establish hidden-weight lazy training, does NOT derive
> parameter movement from coercivity, and does NOT prove the full
> Bach (2024) lazy-NTK theorem. Those require the full lazy-NTK
> model in `LTFP/MathlibExt/Probability/NTKLazyCarrier.lean`.

## Main result

* `randomFeature_exact_lazy_linearization_tail` — for any product
  measure `Measure.pi (fun _ : Fin m => ν)` on the random-feature
  draw space, any pair of measurable parameter trajectories
  `a₀, aₜ` (the output-layer state at times `0` and `t`), and any
  slack `δ ≥ 0`,

      P{ ∃ x, |f(aₜ, x) − (f(a₀, x) + ⟨∇_a f(a₀, x), aₜ − a₀⟩)| > 0 } ≤ δ,

  because by `lazyNet_exact_linearization` the linearization error is
  identically zero for every realization, every input, and every pair
  of parameters — so the bad event is empty.

## Encoding choices

We rename the time-`t` parameter trajectory from `at` to `at_` because
`at` is a Lean keyword (used in tactic targeting). This is a purely
cosmetic rename; the mathematical statement is unchanged.
-/

namespace ProbabilityTheory

open MeasureTheory

/-- **Random-feature exact-linearization tail bound** (B8 N5 random-
feature carrier).

For the output-layer-only random-feature model, the linearization
error at any base point is identically zero (see
`lazyNet_exact_linearization`). Hence the event

  `{ω | ∃ x, 0 < |lazyNet σ ω (aₜ ω) x −
              (lazyNet σ ω (a₀ ω) x +
                ⟨∇_a (lazyNet σ ω · x) (a₀ ω), aₜ ω − a₀ ω⟩)| }`

is empty under *any* product measure on the random-feature draw
space, and is therefore bounded by any non-negative slack `δ`.

This is the cleanest possible lazy-training tail bound: it holds
deterministically (the integrand is zero pointwise), but is stated
in tail form so that downstream consumers can compose with other
probabilistic carriers without an extra wrapper.

The parameter trajectories `a₀` and `at_` may depend arbitrarily on
the random-feature draw `ω`; no measurability or integrability is
needed because the bad event is identically empty. -/
theorem randomFeature_exact_lazy_linearization_tail
    {σ : ℝ → ℝ} {d m : ℕ}
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)}
    {δ : ℝ} (hδ : 0 ≤ δ)
    (a₀ at_ :
      (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) →
        EuclideanSpace ℝ (Fin m)) :
    (Measure.pi (fun _ : Fin m => ν)).real
        {ω | ∃ x : EuclideanSpace ℝ (Fin d),
          0 <
            |lazyNet σ ω (at_ ω) x -
              (lazyNet σ ω (a₀ ω) x +
                inner ℝ
                  (gradient (fun a => lazyNet σ ω a x) (a₀ ω))
                  (at_ ω - a₀ ω))|}
      ≤ δ := by
  -- The bad event is empty: by `lazyNet_exact_linearization`, the
  -- linearization error is zero pointwise, so its absolute value is
  -- zero and cannot be strictly positive.
  have hempty :
      {ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ |
        ∃ x : EuclideanSpace ℝ (Fin d),
          0 <
            |lazyNet σ ω (at_ ω) x -
              (lazyNet σ ω (a₀ ω) x +
                inner ℝ
                  (gradient (fun a => lazyNet σ ω a x) (a₀ ω))
                  (at_ ω - a₀ ω))|}
        = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_exists]
    intro x
    -- Apply exact linearization at (a₀ ω, at_ ω, x): the difference is 0.
    have heq :
        lazyNet σ ω (at_ ω) x =
          lazyNet σ ω (a₀ ω) x +
            inner ℝ (gradient (fun a => lazyNet σ ω a x) (a₀ ω))
              (at_ ω - a₀ ω) :=
      lazyNet_exact_linearization σ ω (a₀ ω) (at_ ω) x
    -- Reduce `|0|` and conclude `¬ 0 < 0`.
    rw [heq, sub_self, abs_zero]
    exact lt_irrefl 0
  -- Rewriting the bad event to `∅` collapses the measure to `0 ≤ δ`.
  rw [hempty, measureReal_empty]
  exact hδ

/-! ## B8 N6 random-feature carrier closure

We package the output-layer-only random-feature loss into the
`randomFeatureRiskFamily` shape and discharge the end-to-end polynomial
generalization bound by composing the random-feature definitions with
the `_pullback` corollary of the wide-network polynomial bound
(see `LTFP/MathlibExt/Probability/WideNetworkDudley.lean`).

The carrier predicate is the bridge identity

  `randomFeatureRiskFamily σ ωrf B_param a p =
    linearizedRiskFamily B_param a (rfFeature σ ωrf p.1, p.2)`,

which lets us pull the linearized-risk polynomial bound back through
the feature map `φ p := (rfFeature σ ωrf p.1, p.2)`.

## Scope (honest)

This closes the **output-layer-only random-feature generalization
carrier**, *conditional on* bounded-feature, bounded-residual,
empirical-norm, measurability/transport, and integrability
hypotheses. It does NOT establish hidden-weight lazy training, full
NTK linearization, or full Bach 2024 lazy-NTK theorem; those are
treated separately in `LTFP/MathlibExt/Probability/NTKLazyCarrier.lean`.
-/

/-- **Random-feature squared-loss family**, indexed by the closed
output-layer parameter ball. The "data point" is
`(x, y) : EuclideanSpace ℝ (Fin d) × ℝ`; the predictor is the lazy
random-feature network `lazyNet σ ωrf a x` and the squared loss is
`(prediction - y)^2`:

  `randomFeatureRiskFamily σ ωrf B_param a (x, y) =
    (lazyNet σ ωrf a.val x - y)^2`.

This is the carrier-shape loss for `EmpiricalFunctionSpace`-style
analysis of the random-feature regime. -/
noncomputable def randomFeatureRiskFamily
    {d q : ℕ} (σ : ℝ → ℝ)
    (ωrf : Fin q → EuclideanSpace ℝ (Fin d) × ℝ) (B_param : ℝ) :
    {a : EuclideanSpace ℝ (Fin q) // ‖a‖ ≤ B_param} →
      EuclideanSpace ℝ (Fin d) × ℝ → ℝ :=
  fun a p => (lazyNet σ ωrf a.val p.1 - p.2) ^ 2

/-- **Bridge identity**: the random-feature squared-loss family equals
the linearized squared-loss family on the feature-mapped data point.

For each parameter `a` and data `p`,

  `randomFeatureRiskFamily σ ωrf B_param a p =
    LTFP.linearizedRiskFamily B_param a (rfFeature σ ωrf p.1, p.2)`.

This is the algebraic key that lets the random-feature carrier inherit
the polynomial Dudley bound for the linearized-risk family by pullback
through the feature map `φ p := (rfFeature σ ωrf p.1, p.2)`. -/
theorem randomFeatureRiskFamily_eq_linearizedRiskFamily_pullback
    {d q : ℕ} (σ : ℝ → ℝ)
    (ωrf : Fin q → EuclideanSpace ℝ (Fin d) × ℝ) (B_param : ℝ)
    (a : {a : EuclideanSpace ℝ (Fin q) // ‖a‖ ≤ B_param})
    (p : EuclideanSpace ℝ (Fin d) × ℝ) :
    randomFeatureRiskFamily σ ωrf B_param a p =
      LTFP.linearizedRiskFamily (d := q) B_param a (rfFeature σ ωrf p.1, p.2) := by
  simp [randomFeatureRiskFamily, LTFP.linearizedRiskFamily, lazyNet_apply]

/-- **Continuity of the random-feature map** in its input argument.
For a continuous activation `σ`, the random-feature vector
`x ↦ rfFeature σ ωrf x` is continuous on `EuclideanSpace ℝ (Fin d)`.

Continuity implies measurability under the standard `BorelSpace`
instance on the finite-dimensional Euclidean space. -/
theorem continuous_rfFeature
    {d q : ℕ} {σ : ℝ → ℝ} (hσ : Continuous σ)
    (ωrf : Fin q → EuclideanSpace ℝ (Fin d) × ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin d) => rfFeature σ ωrf x) := by
  -- Continuity into `EuclideanSpace ℝ (Fin q)` follows from coordinate-wise
  -- continuity via the `PiLp`-product structure.
  apply continuous_induced_rng.mpr
  refine continuous_pi (fun j => ?_)
  -- Each coordinate is `(1/√q) * σ (⟨w_j, x⟩ + b_j)`, continuous as a
  -- composition of continuous maps.
  have h_inner : Continuous
      (fun x : EuclideanSpace ℝ (Fin d) => @inner ℝ _ _ (ωrf j).1 x) :=
    continuous_const.inner continuous_id
  have h_add : Continuous
      (fun x : EuclideanSpace ℝ (Fin d) => @inner ℝ _ _ (ωrf j).1 x + (ωrf j).2) :=
    h_inner.add continuous_const
  have h_sigma : Continuous
      (fun x : EuclideanSpace ℝ (Fin d) =>
        σ (@inner ℝ _ _ (ωrf j).1 x + (ωrf j).2)) := hσ.comp h_add
  have h_scale : Continuous
      (fun x : EuclideanSpace ℝ (Fin d) =>
        (1 / Real.sqrt (q : ℝ)) *
          σ (@inner ℝ _ _ (ωrf j).1 x + (ωrf j).2)) :=
    continuous_const.mul h_sigma
  -- The `j`-th coordinate of `rfFeature σ ωrf x` is this scalar.
  -- Underlying representation: `rfFeature σ ωrf x = WithLp.toLp 2 (fun j => ...)`,
  -- so projecting back via `WithLp.equiv` exposes the scalar coordinate map.
  convert h_scale using 1

/-- **Measurability of the random-feature map** in its input argument,
for a continuous activation. -/
theorem measurable_rfFeature
    {d q : ℕ} {σ : ℝ → ℝ} (hσ : Continuous σ)
    (ωrf : Fin q → EuclideanSpace ℝ (Fin d) × ℝ) :
    Measurable (fun x : EuclideanSpace ℝ (Fin d) => rfFeature σ ωrf x) :=
  (continuous_rfFeature hσ ωrf).measurable

/-- **B8 N6 random-feature carrier closure**: end-to-end polynomial
generalization bound for the random-feature squared-loss family.

The expected uniform deviation of `randomFeatureRiskFamily σ ωrf
B_param` over the closed output-layer parameter ball is bounded by the
explicit polynomial Dudley constant inherited from the linearized-risk
bound through the feature-map pullback.

The hypotheses are the natural composites of those of the underlying
`_pullback` corollary, specialized to the random-feature carrier:

* `hσ : Measurable σ` — needed to assert the feature map's measurability.
* `hbnd_ae` — bounded-loss `μ'`-a.e. condition, where `μ'` is the joint
  law of the feature-mapped pair `(rfFeature σ ωrf x, y)`.
* `hae` — bounded-support `μ'ⁿ`-a.e. bundle.
* `hint` — integrability of the empirical Rademacher complexity
  against the i.i.d. product of `μ'`.

## Honesty note

This theorem closes output-layer-only random-feature *prediction*:
under bounded-feature, bounded-residual, empirical-norm,
measurability/transport, and integrability hypotheses, the expected
uniform deviation has explicit polynomial Dudley rate `O(1/√m)` with
the standard `√(log(2 · (1 + 16 B R B_param / ε)^q))` Vershynin-style
constant. It does NOT establish hidden-weight lazy training, parameter
movement bounds from coercivity, or full Bach 2024 lazy-NTK
generalization. -/
theorem randomFeature_wide_network_generalization_bound
    {d q m : ℕ} {σ : ℝ → ℝ} (hσ : Continuous σ)
    (ωrf : Fin q → EuclideanSpace ℝ (Fin d) × ℝ)
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d) × ℝ))
    [MeasureTheory.IsProbabilityMeasure μ]
    (B_param R B c ε : ℝ)
    (hq : 1 ≤ q)
    (hR_nn : 0 ≤ R) (hB_nn : 0 ≤ B) (hB_param_nn : 0 ≤ B_param)
    (hBR_pos : 0 < 2 * B * R)
    (hε_pos : 0 < ε) (hm_pos : 0 < m) (hεc : ε < c / 2)
    (hbnd_ae :
      ∀ᵐ p : EuclideanSpace ℝ (Fin q) × ℝ
        ∂(MeasureTheory.Measure.map
          (fun p : EuclideanSpace ℝ (Fin d) × ℝ => (rfFeature σ ωrf p.1, p.2)) μ),
        ∀ a : {a : EuclideanSpace ℝ (Fin q) // ‖a‖ ≤ B_param},
        |LTFP.linearizedRiskFamily (d := q) B_param a p| ≤ B ^ 2)
    (hae :
      ∀ᵐ (S : Fin m → EuclideanSpace ℝ (Fin q) × ℝ)
        ∂(MeasureTheory.Measure.pi (fun _ : Fin m =>
          MeasureTheory.Measure.map
            (fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
              (rfFeature σ ωrf p.1, p.2)) μ)),
        (∀ i, ‖(S i).1‖ ≤ R) ∧
        (∀ a : EuclideanSpace ℝ (Fin q), ‖a‖ ≤ B_param →
          ∀ i, |@inner ℝ _ _ a (S i).1 - (S i).2| ≤ B) ∧
        (∀ a : {a : EuclideanSpace ℝ (Fin q) // ‖a‖ ≤ B_param},
          empiricalNorm
              (LTFP.linearizedRiskSample (fun i => (S i).1) (fun i => (S i).2))
            (LTFP.linearizedRiskFamily (d := q) B_param a) ≤ c))
    (hint : MeasureTheory.Integrable
      (fun S : Fin m → EuclideanSpace ℝ (Fin q) × ℝ =>
        empiricalRademacherComplexity m
          (LTFP.linearizedRiskFamily (d := q) B_param) S)
      (MeasureTheory.Measure.pi (fun _ : Fin m =>
        MeasureTheory.Measure.map
          (fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
            (rfFeature σ ωrf p.1, p.2)) μ))) :
    ∫ ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ,
        uniformDeviation m
          (randomFeatureRiskFamily σ ωrf B_param)
          μ id (id ∘ ω)
        ∂(MeasureTheory.Measure.pi (fun _ ↦ μ)) ≤
      2 * (4 * ε + (12 / Real.sqrt m) *
        ((c / 2 - ε) *
          √(Real.log
            (2 * ((⌈(1 + 16 * B * R * B_param / ε) ^ q⌉₊ : ℕ) : ℝ))))) := by
  -- The feature map.
  set φ : EuclideanSpace ℝ (Fin d) × ℝ → EuclideanSpace ℝ (Fin q) × ℝ :=
    fun p => (rfFeature σ ωrf p.1, p.2) with hφ_def
  -- Its measurability.
  have hφ_meas : Measurable φ := by
    rw [hφ_def]
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_rfFeature hσ ωrf).comp measurable_fst
    · exact measurable_snd
  -- Apply the pullback polynomial bound with `d := q` and feature map `φ`.
  have h_pullback :=
    LTFP.wide_network_expected_uniform_deviation_le_explicit_polynomial_paramBall_iid_pullback
      (d := q) (m := m) (Ω := EuclideanSpace ℝ (Fin d) × ℝ) μ φ hφ_meas
      B_param R B c ε hq hR_nn hB_nn hB_param_nn hBR_pos hε_pos hm_pos hεc
      hbnd_ae hae hint
  -- Identify the integrand: `randomFeatureRiskFamily ... a p =
  -- linearizedRiskFamily B_param a (φ p)` (the bridge identity).
  have h_integrand_eq : ∀ ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ,
      uniformDeviation m
          (randomFeatureRiskFamily σ ωrf B_param) μ id (id ∘ ω)
        = uniformDeviation m
            (fun a p => LTFP.linearizedRiskFamily (d := q) B_param a (φ p))
            μ id (id ∘ ω) := by
    intro ω
    simp only [uniformDeviation, Function.comp_apply, id_eq]
    apply congr_arg (iSup ·)
    funext a
    -- Empirical and population terms both equal under the bridge identity.
    have h_sample : ∀ k, randomFeatureRiskFamily σ ωrf B_param a (ω k)
        = LTFP.linearizedRiskFamily (d := q) B_param a (φ (ω k)) := by
      intro k
      exact randomFeatureRiskFamily_eq_linearizedRiskFamily_pullback σ ωrf B_param a (ω k)
    have h_sum_eq : ∑ k : Fin m, randomFeatureRiskFamily σ ωrf B_param a (ω k) =
        ∑ k : Fin m,
          LTFP.linearizedRiskFamily (d := q) B_param a (φ (ω k)) :=
      Finset.sum_congr rfl (fun k _ => h_sample k)
    have h_int_eq : ∫ ω', randomFeatureRiskFamily σ ωrf B_param a ω' ∂μ =
        ∫ ω', LTFP.linearizedRiskFamily (d := q) B_param a (φ ω') ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω'
      exact randomFeatureRiskFamily_eq_linearizedRiskFamily_pullback σ ωrf B_param a ω'
    rw [h_sum_eq, h_int_eq]
  -- Chain.
  calc ∫ ω, uniformDeviation m
              (randomFeatureRiskFamily σ ωrf B_param) μ id (id ∘ ω)
            ∂(MeasureTheory.Measure.pi (fun _ : Fin m => μ))
      = ∫ ω, uniformDeviation m
              (fun a p => LTFP.linearizedRiskFamily (d := q) B_param a (φ p))
              μ id (id ∘ ω)
            ∂(MeasureTheory.Measure.pi (fun _ : Fin m => μ)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with ω
        exact h_integrand_eq ω
    _ ≤ _ := h_pullback

end ProbabilityTheory
