/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import LTFP.MathlibExt.Analysis.Matrix.OpNormByMax

/-!
# Empirical NTK concentration (scalar Hoeffding + union bound)

**B8 Node 4, v1 scope** (per `docs/wiki/B8_N4_STATEMENT.md`,
Codex-confirmed 2026-05-21).

Setting: a one-hidden-layer neural network with width `m`, iid init
`(w_j, b_j) ~ ν` from a truncated-bounded distribution, bounded
activation `σ : ℝ → ℝ` with `|σ z| ≤ σ_inf`. For a fixed finite input
set `xs : Fin n → EuclideanSpace ℝ (Fin d)`, the empirical NTK on
the points `(xs a, xs b)` is

  `K̂_m(a, b) := (1 / m) Σ_{j=1..m} G_j(a, b)`,
  `G_j(a, b)  := σ(⟨w_j, xs a⟩ + b_j) · σ(⟨w_j, xs b⟩ + b_j)`,

and the **population NTK** is `K(a, b) := E G_j(a, b)`. The
empirical version concentrates around the population version at the
scalar-Hoeffding rate `O(n / √m)` in operator norm.

## v1 scope (per Codex confirmation 2026-05-21)

* **Init**: truncated-Gaussian / bounded-support init only —
  `(w_j, b_j)` lives in a fixed bounded set a.s.
* **Activations**: bounded only (`|σ z| ≤ σ_inf`), e.g. tanh, sigmoid.
* **Rate**: `O(n / √m)` is accepted (vs sharper `O(√(log n)/√m)` via
  matrix Bernstein, which would require B6 Lieb concavity).
* **σ' Jacobian term in Bach Eq. 12.29 is dropped** in v1 to keep
  summands clean; can be re-added as a parallel `σ'`-block term in a
  follow-up.

## Main definitions

* `neuronNTK` — single-neuron NTK contribution `σ(⟨w,x⟩+b) σ(⟨w,x'⟩+b)`.
* `empiricalNTK` — width-`m` empirical NTK matrix entry `(a, b)`.
* `populationNTK` — population NTK matrix entry `(a, b)` (integral
  under the init measure).

## Main results

* `neuronNTK_bound` — pointwise bound `|G_j(a, b)| ≤ σ_inf^2` for any
  bounded activation `σ` and any `wb`.
* `neuronNTK_measurable` — measurability of the single-neuron NTK as a
  function of `(w, b)`.
* `neuronNTK_pi_iIndepFun` — under `Measure.pi (fun _ : Fin m => ν)`,
  the family `j ↦ neuronNTK σ x x' (ω j)` is `iIndepFun`.
* `hasSubgaussianMGF_centered_neuronNTK_sum` — the centered scaled
  sum `(1/m) Σ_j (G_j - K(a,b))` is sub-Gaussian with parameter
  `σ_inf^4 / m` (Hoeffding + iid sum + scaling).
* `empiricalNTK_entry_concentration_tail` — per-entry Hoeffding tail
  bound for `|K̂_m(a,b) - K(a,b)|`.
* `empiricalNTK_opNorm_concentration_param` — operator-norm tail
  bound `μ.real { ω | n·ε < ‖K̂_m − K‖_op } ≤ 2 n² · exp(−ε² m /
  (2 σ_inf⁴))`, obtained by composing the per-entry tail with a
  union bound over the `n²` matrix entries and the matrix-norm glue
  lemma `Matrix.l2_opNorm_le_card_mul_of_entry_le` from
  `LTFP/MathlibExt/Analysis/Matrix/OpNormByMax.lean`.
* `ntk_concentration_scalar_hoeffding` — the named-rate form: with
  probability at least `1 − δ`,
  `‖K̂_m − K‖_op ≤ n · σ_inf² · √(2 log(2 n² / δ) / m)`. This is
  the B8 N4 v1 sub-carrier consumed downstream by B8 N5 lazy-
  training analysis.

## B8 N5 v1 status

This file closes the **scalar Hoeffding v1 sub-carrier** for B8 N5
in full: union bound + matrix glue are wired through to the named-
rate statement `ntk_concentration_scalar_hoeffding`.

What remains for a *full* B8 N5 with sharper rates is genuinely
multi-week upstream work, NOT a v1 wiring task:

1. **Matrix Bernstein** to upgrade the rate from `O(n / √m)` to the
   sharper `O(√(log n) / √m)`, which requires B6 Lieb concavity —
   currently a multi-week Mathlib gap.
2. **Carrier-facing wide-network theorem** composing this
   concentration side with the deterministic Taylor remainder
   (`LTFP/MathlibExt/Calculus/TaylorRemainderBallRight.lean`) into a
   wide-network learning rate. The Taylor side is currently 1D
   scalar `f : ℝ → ℝ`; bridging to the multivariate parameter space
   that matches `lazy_training_linearization_from_taylor`
   (`LTFP/MathlibExt/Analysis/LazyTrainingLinearization.lean`)
   requires (a) a multivariate Hessian Taylor bound and (b) a
   parameter-movement bound `‖θt − θ₀‖ ≤ A/√m` derived from this
   NTK concentration. Both are days+ infrastructure, deferred.
-/

namespace ProbabilityTheory

open MeasureTheory NNReal Real BigOperators

variable {d : ℕ}

/-- **Single-neuron NTK contribution** (`σ`-block only, v1 scope).

Given a bounded activation `σ : ℝ → ℝ`, inputs `x, x' ∈ ℝᵈ`, and a
weight-bias pair `wb = (w, b)`, the single-neuron NTK contribution is
`σ(⟨w, x⟩ + b) · σ(⟨w, x'⟩ + b)`. -/
noncomputable def neuronNTK (σ : ℝ → ℝ) (x x' : EuclideanSpace ℝ (Fin d))
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  σ (inner ℝ wb.1 x + wb.2) * σ (inner ℝ wb.1 x' + wb.2)

/-- **Width-`m` empirical NTK matrix entry** at `(a, b)`.

Given an iid sample `ω : Fin m → (ℝᵈ × ℝ)` of weight-bias pairs,
the empirical NTK at the pair `(xs a, xs b)` is the sample average
`(1/m) Σⱼ neuronNTK σ (xs a) (xs b) (ω j)`. -/
noncomputable def empiricalNTK (σ : ℝ → ℝ) {n : ℕ}
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) {m : ℕ}
    (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun a b => (1 / (m : ℝ)) * ∑ j, neuronNTK σ (xs a) (xs b) (ω j)

/-- **Population NTK matrix entry** at `(a, b)`.

Given an init measure `ν` on `(ℝᵈ × ℝ)`, the population NTK at the
pair `(xs a, xs b)` is `E_{wb ~ ν} neuronNTK σ (xs a) (xs b) wb`. -/
noncomputable def populationNTK (σ : ℝ → ℝ) {n : ℕ}
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun a b => ∫ wb, neuronNTK σ (xs a) (xs b) wb ∂ν

/-! ### Boundedness and measurability -/

/-- **Pointwise bound on the single-neuron NTK.** For any bounded
activation `|σ z| ≤ σ_inf` and any `wb`,
`|neuronNTK σ x x' wb| ≤ σ_inf * σ_inf`. -/
theorem neuronNTK_bound {σ : ℝ → ℝ} {σ_inf : ℝ} (hσ_nn : 0 ≤ σ_inf)
    (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    (x x' : EuclideanSpace ℝ (Fin d))
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    |neuronNTK σ x x' wb| ≤ σ_inf * σ_inf := by
  unfold neuronNTK
  rw [abs_mul]
  exact mul_le_mul (hσ_bdd _) (hσ_bdd _) (abs_nonneg _) hσ_nn

/-- **Measurability of the single-neuron NTK.** If `σ` is measurable,
then `wb ↦ neuronNTK σ x x' wb` is measurable. -/
theorem neuronNTK_measurable {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    (x x' : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
      neuronNTK σ x x' wb) := by
  unfold neuronNTK
  have h_w_meas : Measurable (fun wb : EuclideanSpace ℝ (Fin d) × ℝ => wb.1) :=
    measurable_fst
  have h_b_meas : Measurable (fun wb : EuclideanSpace ℝ (Fin d) × ℝ => wb.2) :=
    measurable_snd
  have h_inner_x : Measurable (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
      inner ℝ wb.1 x) := by
    have : Continuous (fun w : EuclideanSpace ℝ (Fin d) => inner ℝ w x) :=
      continuous_inner.comp (Continuous.prodMk continuous_id continuous_const)
    exact this.measurable.comp h_w_meas
  have h_inner_x' : Measurable (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
      inner ℝ wb.1 x') := by
    have : Continuous (fun w : EuclideanSpace ℝ (Fin d) => inner ℝ w x') :=
      continuous_inner.comp (Continuous.prodMk continuous_id continuous_const)
    exact this.measurable.comp h_w_meas
  have h_pre_x : Measurable (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
      inner ℝ wb.1 x + wb.2) := h_inner_x.add h_b_meas
  have h_pre_x' : Measurable (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
      inner ℝ wb.1 x' + wb.2) := h_inner_x'.add h_b_meas
  exact (hσ_meas.comp h_pre_x).mul (hσ_meas.comp h_pre_x')

/-! ### Independence under the product measure -/

variable {n m : ℕ}

/-- **Independence of the per-neuron NTK family under product
initialization.** Under `Measure.pi (fun _ : Fin m => ν)`, the family
`j ↦ neuronNTK σ (xs a) (xs b) (ω j)` is `iIndepFun`. -/
theorem neuronNTK_pi_iIndepFun
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    (x x' : EuclideanSpace ℝ (Fin d))
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν] :
    iIndepFun
      (fun j (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) =>
        neuronNTK σ x x' (ω j))
      (Measure.pi (fun _ : Fin m => ν)) := by
  -- Use `iIndepFun_pi` for the projection family and then compose with
  -- `neuronNTK σ x x'`.
  have h_proj : iIndepFun
      (fun (j : Fin m) (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) => ω j)
      (Measure.pi (fun _ : Fin m => ν)) := by
    have := iIndepFun_pi (μ := fun _ : Fin m => ν)
      (X := fun _ wb => wb) (mX := fun _ => aemeasurable_id)
    exact this
  -- Compose with `neuronNTK σ x x'`.
  have h_meas := neuronNTK_measurable hσ_meas x x'
  have := h_proj.comp (fun _ wb => neuronNTK σ x x' wb) (fun _ => h_meas)
  exact this

/-! ### Per-pair Hoeffding sub-Gaussian moment -/

/-- **Per-pair centered Hoeffding sub-Gaussian.** Under the product
init `Measure.pi (fun _ : Fin m => ν)`, for any pair of inputs
`x, x'` the centered single-neuron contribution
`ω ↦ neuronNTK σ x x' (ω j) - E[neuronNTK σ x x' wb]` has a
sub-Gaussian moment-generating function with proxy
`((σ_inf^2 - (-σ_inf^2)) / 2)^2 = σ_inf^4`. This is **Hoeffding's lemma**
applied to a bounded random variable.

Note this is a single-neuron result; the empirical NTK is the
average over `j = 1..m`. The sum/average is handled by
`hasSubgaussianMGF_centered_neuronNTK_sum` below. -/
theorem hasSubgaussianMGF_centered_neuronNTK
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {σ_inf : ℝ} (hσ_pos : 0 < σ_inf) (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    (x x' : EuclideanSpace ℝ (Fin d))
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν]
    (j : Fin m) :
    HasSubgaussianMGF
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        neuronNTK σ x x' (ω j) -
          ∫ wb, neuronNTK σ x x' wb ∂ν)
      ⟨σ_inf ^ 4, by positivity⟩
      (Measure.pi (fun _ : Fin m => ν)) := by
  set σ_inf_sq : ℝ := σ_inf * σ_inf with hσ_inf_sq
  have hσ_nn : 0 ≤ σ_inf := le_of_lt hσ_pos
  have hσ_sq_nn : 0 ≤ σ_inf_sq := mul_nonneg hσ_nn hσ_nn
  -- Build the measure on the product space.
  let μ : Measure (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :=
    Measure.pi (fun _ : Fin m => ν)
  have : IsProbabilityMeasure μ := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Fin m => ν))
    infer_instance
  -- The single-neuron contribution, as a function of ω.
  let Y : (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ :=
    fun ω => neuronNTK σ x x' (ω j)
  -- Boundedness: `Y ω ∈ [-σ_inf², σ_inf²]` almost surely.
  have hY_bdd_pt : ∀ ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ,
      Y ω ∈ Set.Icc (-σ_inf_sq) σ_inf_sq := by
    intro ω
    have hb : |neuronNTK σ x x' (ω j)| ≤ σ_inf_sq :=
      neuronNTK_bound hσ_nn hσ_bdd x x' (ω j)
    exact abs_le.mp hb
  have hY_bdd : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (-σ_inf_sq) σ_inf_sq :=
    Filter.Eventually.of_forall hY_bdd_pt
  -- Measurability of `Y`.
  have hY_meas : Measurable Y := by
    have h_eval : Measurable (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        ω j) := measurable_pi_apply _
    exact (neuronNTK_measurable hσ_meas x x').comp h_eval
  -- Apply Hoeffding for bounded RVs (the centered form).
  have h_hoeff : HasSubgaussianMGF
      (fun ω => Y ω - ∫ ω', Y ω' ∂μ)
      ((‖σ_inf_sq - (-σ_inf_sq)‖₊ / 2) ^ 2) μ :=
    hasSubgaussianMGF_of_mem_Icc hY_meas.aemeasurable hY_bdd
  -- Identify `∫ Y dμ = ∫ neuronNTK σ x x' wb dν` (via Measure.pi
  -- integration), and identify the Hoeffding proxy with `σ_inf^4`.
  have h_proxy_eq : ((‖σ_inf_sq - (-σ_inf_sq)‖₊ / 2) ^ 2 : ℝ≥0)
      = ⟨σ_inf ^ 4, by positivity⟩ := by
    apply NNReal.eq
    push_cast
    have h1 : σ_inf_sq - (-σ_inf_sq) = 2 * σ_inf_sq := by ring
    rw [h1]
    rw [show ‖(2 : ℝ) * σ_inf_sq‖ = 2 * σ_inf_sq by
      rw [Real.norm_eq_abs]
      have h2sq_nn : 0 ≤ 2 * σ_inf_sq := by positivity
      exact abs_of_nonneg h2sq_nn]
    have hσ_sq_explicit : σ_inf_sq = σ_inf ^ 2 := by
      rw [hσ_inf_sq]; ring
    rw [hσ_sq_explicit]
    ring
  rw [h_proxy_eq] at h_hoeff
  -- Identify `∫ Y dμ` with `∫ neuronNTK σ x x' wb ∂ν`.
  have h_integral_eq : ∫ ω, Y ω ∂μ = ∫ wb, neuronNTK σ x x' wb ∂ν := by
    -- `Y ω = neuronNTK σ x x' (ω j)` and integration over `Measure.pi` along
    -- the `j`-th coordinate equals integration on the marginal.
    have h_marg : ∫ ω, neuronNTK σ x x' (ω j) ∂μ
        = ∫ wb, neuronNTK σ x x' wb ∂ν := by
      have h_meas_pre : Measurable (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
          neuronNTK σ x x' wb) := neuronNTK_measurable hσ_meas x x'
      -- `μ.map (fun ω => ω j) = ν` for product measures, by
      -- `measurePreserving_eval` for probability measures.
      have h_push : μ.map (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ => ω j) = ν := by
        show (Measure.pi (fun _ : Fin m => ν)).map (Function.eval j) = ν
        exact (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin m => ν) j).map_eq
      have h_integral : ∫ ω, neuronNTK σ x x' (ω j) ∂μ
          = ∫ wb, neuronNTK σ x x' wb ∂μ.map (fun ω => ω j) := by
        rw [integral_map (measurable_pi_apply _).aemeasurable h_meas_pre.aestronglyMeasurable]
      rw [h_integral, h_push]
    show ∫ ω, neuronNTK σ x x' (ω j) ∂μ = ∫ wb, neuronNTK σ x x' wb ∂ν
    exact h_marg
  rw [h_integral_eq] at h_hoeff
  exact h_hoeff

/-! ### Per-entry concentration -- sub-Gaussian sum -/

/-- **Per-entry Hoeffding sub-Gaussian** for the empirical-minus-population
NTK at a fixed pair `(a, b)`.

By Hoeffding's lemma the per-neuron centered contribution has
sub-Gaussian proxy `σ_inf^4`. Summing `m` iid sub-Gaussians and scaling
by `1/m` gives proxy `σ_inf^4 / m` for the centered scaled sum
`(1/m) Σⱼ (G_j - E G_j) = K̂_m(a,b) - K(a,b)`. -/
theorem hasSubgaussianMGF_empiricalNTK_entry
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {σ_inf : ℝ} (hσ_pos : 0 < σ_inf) (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    {n : ℕ} (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {m : ℕ} (hm : 0 < m)
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν]
    (a b : Fin n) :
    HasSubgaussianMGF
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        empiricalNTK σ xs ω a b - populationNTK σ xs ν a b)
      ⟨σ_inf ^ 4 / (m : ℝ), by positivity⟩
      (Measure.pi (fun _ : Fin m => ν)) := by
  set μ : Measure (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :=
    Measure.pi (fun _ : Fin m => ν) with hμ_def
  haveI : IsProbabilityMeasure μ := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Fin m => ν))
    infer_instance
  -- Centered per-neuron family.
  set Y : Fin m → (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ :=
    fun j ω => neuronNTK σ (xs a) (xs b) (ω j) -
      ∫ wb, neuronNTK σ (xs a) (xs b) wb ∂ν with hY_def
  -- Each centered summand is sub-Gaussian with proxy σ_inf^4 (Hoeffding).
  have hY_subG : ∀ j : Fin m,
      HasSubgaussianMGF (Y j) ⟨σ_inf ^ 4, by positivity⟩ μ := by
    intro j
    exact hasSubgaussianMGF_centered_neuronNTK hσ_meas hσ_pos hσ_bdd (xs a) (xs b) j
  -- The Y_j are iIndepFun (composed projection family).
  have hY_indep : iIndepFun Y μ := by
    have h_proj : iIndepFun
        (fun j (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) =>
          neuronNTK σ (xs a) (xs b) (ω j)) μ := by
      exact neuronNTK_pi_iIndepFun hσ_meas (xs a) (xs b)
    -- Subtract a constant: composition with `· - c`.
    have hY_eq : Y = fun j => (fun (r : ℝ) =>
        r - ∫ wb, neuronNTK σ (xs a) (xs b) wb ∂ν) ∘
        (fun (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) =>
          neuronNTK σ (xs a) (xs b) (ω j)) := by
      funext j ω
      simp [hY_def, Function.comp]
    rw [hY_eq]
    exact h_proj.comp _ (fun _ => measurable_id.sub_const _)
  -- Sum of iid sub-Gaussians: proxy `m · σ_inf^4`.
  have hSum_subG : HasSubgaussianMGF (fun ω => ∑ j, Y j ω)
      (∑ _j : Fin m, (⟨σ_inf ^ 4, by positivity⟩ : ℝ≥0)) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hY_indep (fun j _ => hY_subG j)
  -- Simplify the sum of constants.
  have h_sum_const :
      (∑ _j : Fin m, (⟨σ_inf ^ 4, by positivity⟩ : ℝ≥0))
        = ⟨(m : ℝ) * σ_inf ^ 4, by positivity⟩ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    apply NNReal.eq
    rw [NNReal.coe_nsmul, NNReal.coe_mk, nsmul_eq_mul]
    push_cast; ring
  rw [h_sum_const] at hSum_subG
  -- Scale by `1/m`: proxy `(1/m)^2 · m · σ_inf^4 = σ_inf^4 / m`.
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hAvg_subG : HasSubgaussianMGF
      (fun ω => (1 / (m : ℝ)) * ∑ j, Y j ω)
      (⟨(1 / (m : ℝ)) ^ 2, sq_nonneg _⟩ *
        ⟨(m : ℝ) * σ_inf ^ 4, by positivity⟩) μ :=
    hSum_subG.const_mul (1 / (m : ℝ))
  -- Simplify the scaled proxy: `(1/m)^2 · (m · σ_inf^4) = σ_inf^4 / m`.
  have h_proxy_final :
      (⟨(1 / (m : ℝ)) ^ 2, sq_nonneg _⟩ *
        ⟨(m : ℝ) * σ_inf ^ 4, by positivity⟩ : ℝ≥0)
        = ⟨σ_inf ^ 4 / (m : ℝ), by positivity⟩ := by
    apply NNReal.eq
    push_cast
    field_simp
  rw [h_proxy_final] at hAvg_subG
  -- Identify the scaled-sum form with `empiricalNTK - populationNTK`.
  refine hAvg_subG.congr ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  -- `(1/m) Σ (G_j - K) = (1/m) Σ G_j - K` because the centering is constant.
  show (1 / (m : ℝ)) * ∑ j, Y j ω
    = empiricalNTK σ xs ω a b - populationNTK σ xs ν a b
  unfold empiricalNTK populationNTK
  set K_ab : ℝ := ∫ wb, neuronNTK σ (xs a) (xs b) wb ∂ν with hK_ab
  -- Sum splits: Σ (G - K) = Σ G - m * K.
  have h_sum_split :
      ∑ j, Y j ω = ∑ j, neuronNTK σ (xs a) (xs b) (ω j) - (m : ℝ) * K_ab := by
    simp only [hY_def]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [h_sum_split]
  field_simp

/-- **Per-entry empirical-NTK tail bound (Hoeffding).** For a fixed
pair `(a, b)` and any `ε ≥ 0`, the probability that the centred
empirical NTK exceeds `ε` is bounded by
`exp(-m · ε² / (2 σ_inf^4))`. -/
theorem empiricalNTK_entry_concentration_tail
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {σ_inf : ℝ} (hσ_pos : 0 < σ_inf) (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    {n : ℕ} (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {m : ℕ} (hm : 0 < m)
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν]
    (a b : Fin n) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin m => ν)).real
        { ω | ε ≤ empiricalNTK σ xs ω a b - populationNTK σ xs ν a b }
      ≤ Real.exp (- ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) := by
  have h_subG := hasSubgaussianMGF_empiricalNTK_entry
    hσ_meas hσ_pos hσ_bdd xs hm a b (ν := ν)
  exact h_subG.measure_ge_le hε

/-- **Per-entry two-sided Hoeffding tail bound.** For the empirical-
minus-population NTK at a fixed pair, the absolute deviation exceeds
`ε` with probability at most `2 exp(-m ε² / (2 σ_inf^4))`. -/
theorem empiricalNTK_entry_concentration_abs_tail
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {σ_inf : ℝ} (hσ_pos : 0 < σ_inf) (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    {n : ℕ} (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {m : ℕ} (hm : 0 < m)
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν]
    (a b : Fin n) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin m => ν)).real
        { ω | ε ≤ |empiricalNTK σ xs ω a b - populationNTK σ xs ν a b| }
      ≤ 2 * Real.exp (- ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) := by
  set μ : Measure (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :=
    Measure.pi (fun _ : Fin m => ν) with hμ_def
  haveI : IsProbabilityMeasure μ := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Fin m => ν))
    infer_instance
  set f : (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ :=
    fun ω => empiricalNTK σ xs ω a b - populationNTK σ xs ν a b with hf_def
  -- Decompose `|f| ≥ ε` into `f ≥ ε` ∪ `-f ≥ ε`.
  have h_subG := hasSubgaussianMGF_empiricalNTK_entry
    hσ_meas hσ_pos hσ_bdd xs hm a b (ν := ν)
  have h_subG_neg := h_subG.neg
  have h_right : μ.real { ω | ε ≤ f ω }
      ≤ Real.exp (-ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) := by
    have h := h_subG.measure_ge_le hε
    simpa [hf_def] using h
  have h_left : μ.real { ω | ε ≤ -f ω }
      ≤ Real.exp (-ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) := by
    have h := h_subG_neg.measure_ge_le hε
    simpa [hf_def, Pi.neg_apply] using h
  -- Union bound on the two events.
  have h_union : { ω | ε ≤ |f ω| } ⊆ { ω | ε ≤ f ω } ∪ { ω | ε ≤ -f ω } := by
    intro ω hω
    have hω' : ε ≤ |f ω| := hω
    by_cases h1 : 0 ≤ f ω
    · left
      have habs : |f ω| = f ω := abs_of_nonneg h1
      show ε ≤ f ω
      rw [← habs]; exact hω'
    · right
      push_neg at h1
      have habs : |f ω| = -f ω := abs_of_neg h1
      show ε ≤ -f ω
      rw [← habs]; exact hω'
  calc μ.real { ω | ε ≤ |f ω| }
      ≤ μ.real ({ ω | ε ≤ f ω } ∪ { ω | ε ≤ -f ω }) :=
        measureReal_mono h_union (measure_ne_top μ _)
    _ ≤ μ.real { ω | ε ≤ f ω } + μ.real { ω | ε ≤ -f ω } :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ))))
            + Real.exp (-ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) := by
        linarith
    _ = 2 * Real.exp (-ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) := by ring

/-! ### Union-bound + matrix-norm composition: the A-class theorem -/

open scoped Matrix.Norms.L2Operator

/-- **Empirical NTK concentration in operator norm (parametric form).**

Under the v1 hypotheses (bounded activation, truncated/bounded init,
fixed input set), the empirical NTK matrix and the population NTK
matrix agree to within `n · ε` in `l²` operator norm with probability
at least `1 - 2 n² · exp(-m ε² / (2 σ_inf^4))`.

This is the per-entry Hoeffding tail bound combined with:
1. A union bound over the `n²` matrix entries.
2. The matrix glue lemma `Matrix.l2_opNorm_le_card_mul_of_entry_le`
   reducing operator-norm control to entrywise control.

To recover the named-rate form (with `δ` instead of an explicit
exponent), set `ε := σ_inf² · √(2 log(2 n² / δ) / m)`. -/
theorem empiricalNTK_opNorm_concentration_param
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {σ_inf : ℝ} (hσ_pos : 0 < σ_inf) (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    {n : ℕ} (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {m : ℕ} (hm : 0 < m)
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν]
    {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin m => ν)).real
        { ω | (n : ℝ) * ε < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖ }
      ≤ 2 * (n : ℝ) ^ 2 * Real.exp (- ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) := by
  set μ : Measure (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :=
    Measure.pi (fun _ : Fin m => ν) with hμ_def
  haveI : IsProbabilityMeasure μ := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Fin m => ν))
    infer_instance
  -- Set Δ ω = empiricalNTK σ xs ω - populationNTK σ xs ν.
  set Δ : (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) →
      Matrix (Fin n) (Fin n) ℝ :=
    fun ω => empiricalNTK σ xs ω - populationNTK σ xs ν with hΔ_def
  -- Bad event: ‖Δ ω‖ > n · ε.
  -- If every entry is ≤ ε, then ‖Δ ω‖ ≤ n · ε by glue lemma.
  -- Contrapositive: ‖Δ ω‖ > n · ε ⟹ ∃ a b, ε < ‖Δ ω a b‖.
  have h_contra : ∀ ω, (n : ℝ) * ε < ‖Δ ω‖ →
      ∃ a b : Fin n, ε < |Δ ω a b| := by
    intro ω hbad
    by_contra h_all
    push_neg at h_all
    have h_all' : ∀ a b : Fin n, ‖Δ ω a b‖ ≤ ε := by
      intro a b
      have := h_all a b
      simpa [Real.norm_eq_abs] using this
    have h_bound :=
      Matrix.l2_opNorm_le_card_mul_of_entry_le (Δ ω) (le_of_lt hε) h_all'
    rw [Fintype.card_fin] at h_bound
    linarith
  -- Set inclusion: { ω | n ε < ‖Δ ω‖ } ⊆ ⋃ (ab : Fin n × Fin n), { ω | ε ≤ |Δ ω a b| }.
  have h_subset : { ω | (n : ℝ) * ε < ‖Δ ω‖ } ⊆
      ⋃ (ab : Fin n × Fin n), { ω | ε ≤ |Δ ω ab.1 ab.2| } := by
    intro ω hω
    obtain ⟨a, b, h_ab⟩ := h_contra ω hω
    refine Set.mem_iUnion.mpr ⟨(a, b), ?_⟩
    exact le_of_lt h_ab
  -- Each entry's tail: μ.real { ω | ε ≤ |Δ_{ab} ω| } ≤ 2 exp(...).
  have h_each : ∀ ab : Fin n × Fin n,
      μ.real { ω | ε ≤ |Δ ω ab.1 ab.2| }
        ≤ 2 * Real.exp (-ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) := by
    intro ab
    have h := empiricalNTK_entry_concentration_abs_tail
      hσ_meas hσ_pos hσ_bdd xs hm ab.1 ab.2 (le_of_lt hε) (ν := ν)
    -- The set form matches by definition of Δ.
    have heq : { ω | ε ≤ |Δ ω ab.1 ab.2| } =
        { ω | ε ≤ |empiricalNTK σ xs ω ab.1 ab.2 -
                  populationNTK σ xs ν ab.1 ab.2| } := by
      ext ω
      simp [hΔ_def, Matrix.sub_apply]
    rw [heq]
    exact h
  -- Combine: union bound + each-entry bound.
  calc μ.real { ω | (n : ℝ) * ε < ‖Δ ω‖ }
      ≤ μ.real (⋃ (ab : Fin n × Fin n), { ω | ε ≤ |Δ ω ab.1 ab.2| }) :=
        measureReal_mono h_subset (measure_ne_top μ _)
    _ ≤ ∑ ab : Fin n × Fin n, μ.real { ω | ε ≤ |Δ ω ab.1 ab.2| } :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ab : Fin n × Fin n,
          2 * Real.exp (-ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) :=
        Finset.sum_le_sum fun ab _ => h_each ab
    _ = (Fintype.card (Fin n × Fin n) : ℝ) *
          (2 * Real.exp (-ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ))))) := by
        rw [Finset.sum_const, Finset.card_univ]
        ring
    _ = 2 * (n : ℝ) ^ 2 * Real.exp (-ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) := by
        rw [Fintype.card_prod, Fintype.card_fin]
        push_cast; ring

/-- **B8 N4 V1 -- Empirical NTK scalar-Hoeffding concentration
(named-rate form).**

Specialization of `empiricalNTK_opNorm_concentration_param` to the
named rate `‖K̂_m − K‖_op ≤ n · σ_inf² · √(2 log(2 n² / δ) / m)` with
confidence at least `1 − δ`. -/
theorem ntk_concentration_scalar_hoeffding
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {σ_inf : ℝ} (hσ_pos : 0 < σ_inf) (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    {n : ℕ} (hn : 0 < n) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {m : ℕ} (hm : 0 < m)
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    (Measure.pi (fun _ : Fin m => ν)).real
        { ω | (n : ℝ) *
              (σ_inf ^ 2 * Real.sqrt (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ)))
            < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖ }
      ≤ δ := by
  -- Set `ε := σ_inf² · √(2 log(2 n² / δ) / m)`.
  -- Then `2 n² · exp(-ε² / (2 σ_inf⁴ / m)) = 2 n² · exp(-log(2 n² / δ)) = δ`.
  set t : ℝ := 2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ) with ht_def
  -- Positivity of t: 2 n² / δ > 2 > 1 since n ≥ 1 and δ < 1, so log > 0.
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hn_sq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have h_2n_sq_pos : (0 : ℝ) < 2 * (n : ℝ) ^ 2 := by positivity
  have h_ratio_pos : (0 : ℝ) < 2 * (n : ℝ) ^ 2 / δ := by positivity
  -- 2 n² / δ ≥ 2 since n ≥ 1, δ < 1.
  have h_ratio_ge : (1 : ℝ) < 2 * (n : ℝ) ^ 2 / δ := by
    have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn_sq_ge_one : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h_num_ge_two : (2 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by linarith
    calc (1 : ℝ) < 2 / δ := by
          rw [lt_div_iff₀ hδ_pos]
          linarith
      _ ≤ 2 * (n : ℝ) ^ 2 / δ := by
          rw [div_le_div_iff_of_pos_right hδ_pos]
          linarith
  -- log(2 n² / δ) > 0.
  have h_log_pos : 0 < Real.log (2 * (n : ℝ) ^ 2 / δ) :=
    Real.log_pos h_ratio_ge
  have ht_pos : 0 < t := by
    rw [ht_def]
    positivity
  set ε : ℝ := σ_inf ^ 2 * Real.sqrt t with hε_def
  have hε_pos : 0 < ε := by
    rw [hε_def]
    exact mul_pos (by positivity) (Real.sqrt_pos.mpr ht_pos)
  -- Apply the parametric bound.
  have h_param := empiricalNTK_opNorm_concentration_param
    hσ_meas hσ_pos hσ_bdd xs hm hε_pos (ν := ν)
  -- Simplify the exponent: ε² / (2 σ_inf⁴ / m) = m · t / 2.
  -- So exp(-ε² / (2 σ_inf⁴ / m)) = exp(-m · t / 2) = exp(-log(2n²/δ)) = δ / (2n²).
  have hσ_sq_pos : (0 : ℝ) < σ_inf ^ 2 := by positivity
  have hσ_4_pos : (0 : ℝ) < σ_inf ^ 4 := by positivity
  have hε_sq : ε ^ 2 = σ_inf ^ 4 * t := by
    rw [hε_def, mul_pow]
    rw [Real.sq_sqrt (le_of_lt ht_pos)]
    ring
  have h_exp_simp :
      Real.exp (-ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) = δ / (2 * (n : ℝ) ^ 2) := by
    rw [hε_sq]
    have h_quot : -(σ_inf ^ 4 * t) / (2 * (σ_inf ^ 4 / (m : ℝ)))
        = -((m : ℝ) * t) / 2 := by
      have hσ_4_ne : σ_inf ^ 4 ≠ 0 := ne_of_gt hσ_4_pos
      have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
      field_simp
    rw [h_quot, ht_def]
    -- exp(-(m · 2 log(2n²/δ) / m) / 2) = exp(-log(2n²/δ)) = δ / (2n²).
    have h_mt : (m : ℝ) * (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ))
        = 2 * Real.log (2 * (n : ℝ) ^ 2 / δ) := by
      field_simp
    rw [h_mt]
    have : (-(2 * Real.log (2 * (n : ℝ) ^ 2 / δ)) / 2)
        = -Real.log (2 * (n : ℝ) ^ 2 / δ) := by ring
    rw [this]
    rw [Real.exp_neg, Real.exp_log h_ratio_pos]
    have h2n_ne : (2 * (n : ℝ) ^ 2 : ℝ) ≠ 0 := ne_of_gt h_2n_sq_pos
    have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
    field_simp
  -- Now finish.
  have h_2n_sq_pos' : (0 : ℝ) < 2 * (n : ℝ) ^ 2 := h_2n_sq_pos
  have h_final : 2 * (n : ℝ) ^ 2 *
      Real.exp (-ε ^ 2 / (2 * (σ_inf ^ 4 / (m : ℝ)))) = δ := by
    rw [h_exp_simp]
    field_simp
  -- Substitute ε in the parametric statement.
  show (Measure.pi (fun _ : Fin m => ν)).real _ ≤ δ
  have h_target : { ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ |
      (n : ℝ) * (σ_inf ^ 2 *
        Real.sqrt (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ)))
      < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖ }
      = { ω | (n : ℝ) * ε < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖ } := by
    ext ω
    simp [hε_def, ht_def]
  rw [h_target]
  exact le_of_le_of_eq h_param h_final

end ProbabilityTheory
