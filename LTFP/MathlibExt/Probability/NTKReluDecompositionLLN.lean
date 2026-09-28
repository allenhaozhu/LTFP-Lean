/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.IdentDistrib
import LTFP.MathlibExt.Probability.NTKConcentration
import LTFP.MathlibExt.Probability.GradNeuronNTK

/-!
# JGH decomposition + Law of Large Numbers for the empirical NTK (T5a-L4)

This file proves the almost-sure convergence of the width-`p` empirical
NTK to the population NTK as `p → ∞`, using the strong law of large
numbers applied to the two separately: the sigma-block
`(1/p) Σ σ(⟨w_k, x⟩) σ(⟨w_k, y⟩)` and the sigma'-block
`(1/p) Σ σ'(⟨w_k, x⟩) σ'(⟨w_k, y⟩) · ⟨x, y⟩`. In the JGH-2018
notation, the empirical NTK

  `Θ̂_p(x, y) := (1/p) Σ_{k=0}^{p-1}
      [σ(⟨w_k, x⟩) σ(⟨w_k, y⟩) + σ'(⟨w_k, x⟩) σ'(⟨w_k, y⟩) · ⟨x, y⟩]`

converges almost surely (under the product measure `infinitePi ν` on
`ℕ → EuclideanSpace ℝ (Fin d) × ℝ`) to the population NTK

  `Θ(x, y) := ∫ σ(⟨w, x⟩) σ(⟨w, y⟩) dν + ∫ σ'(⟨w, x⟩) σ'(⟨w, y⟩) dν
                · ⟨x, y⟩`.

## Setting

We work with a general **bounded** activation `σ` with **bounded**
derivative `σ'` (both measurable). The choice of activation is left
free — L4 is activation-agnostic; the closed-form ReLU NTK integral
comes later in L3 (Cho–Saul).

Note on the JGH `a_k`-block. In the two-layer network
`f(θ, x) = (1/√p) Σ_k a_k σ(⟨w_k, x⟩)`, the parameter gradient
decomposes as
`⟨∇f(x), ∇f(y)⟩ = (1/p) Σ σ(⟨w_k, x⟩) σ(⟨w_k, y⟩)
                + (1/p) Σ a_k^2 σ'(⟨w_k, x⟩) σ'(⟨w_k, y⟩) ⟨x, y⟩`
(this deterministic identity is already established in
`LTFP/MathlibExt/Probability/FullNetwork.lean`, viz.
`fullTrainingKernel_init_eq_empiricalFullNTK` at initialization
`InitParam a₀ w₀` with `a_j^2 = 1`, so the `a_k^2` factor collapses).
Since T5a-L4 is stated at initialization with `a_k ∈ {±1}` (or any
distribution with `𝔼[a^2] = 1`), the `a_k^2`-block simplifies to the
`σ'`-block in expectation — matching Bach Eq. 12.29 and JGH 2018 §3.1.

## Main definitions

* `iidInit d ν` — the product measure `infinitePi (fun _ : ℕ => ν)`
  on `ℕ → EuclideanSpace ℝ (Fin d) × ℝ`, modelling an infinite iid
  sample of weight-bias pairs.

## Main results

* `neuronNTK_strong_law_ae` — the almost-sure limit of the empirical
  σ-block sample average:
  `∀ᵐ ω, Tendsto (fun p => (1/p) Σ_{k < p} σ(⟨(ω k).1, x⟩ + (ω k).2)
                                       * σ(⟨(ω k).1, y⟩ + (ω k).2))
    atTop (𝓝 (∫ σ(⟨w, x⟩ + b) σ(⟨w, y⟩ + b) dν))`.
* `gradNeuronNTK_strong_law_ae` — the analogous almost-sure limit for
  the σ'-block sample average.
* `empiricalFullNTK_scalar_strong_law_ae` — the JGH decomposition +
  LLN combined: the width-`p` empirical NTK sample-average scalar
  entry `(x, y)` converges almost surely to the population NTK entry.

## Proof outline

The strong-law application is entry-wise, per pair `(x, y)`, and uses
`ProbabilityTheory.strong_law_ae_real` on the ℕ-indexed sequence of
neuron contributions. The three hypotheses are dispatched:

1. **Integrability** — `neuronNTK σ x y` and `gradNeuronNTK σ' x y`
   are bounded (by `σ_inf²` and `M'^2 · G` respectively), hence
   integrable against any probability measure.
2. **Pairwise independence** — under `infinitePi ν`, the family
   `k ↦ (ω ↦ f (ω k))` is `iIndepFun` (via
   `ProbabilityTheory.iIndepFun_infinitePi`), which implies pairwise
   `IndepFun` (via `.indepFun`).
3. **Identical distribution** — each `X_k := ω ↦ f (ω k)` has the
   same law as `X_0`, because the coordinate maps `ω ↦ ω k` are
   equidistributed under `infinitePi (fun _ => ν)`.

The expectation `𝔼[X_0]` is identified with `∫ f wb ∂ν` via
`measurePreserving_eval_infinitePi` and `integral_map`.

## Downstream use

This L4 result is a foundational input to T5a-L2 (ReLU NTK closed-form
integral): combined with L3 (Cho–Saul), one obtains the closed-form
`Θ(x, y) = (‖x‖‖y‖ / 2π) · (√(1-u²) + u(π - arccos u))` from a
finite-width, a.s. limit statement. It is also the missing link in
Bach Eq. 12.29 § between the finite-width empirical NTK and the
infinite-width population NTK.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset Function
open scoped BigOperators Topology NNReal

namespace LTFP.MathlibExt.Probability

variable {d : ℕ}

/-! ### Setup: infinite iid product measure -/

/-- **Infinite iid initialization measure.** The product measure on
`ℕ → (ℝᵈ × ℝ)` obtained by taking iid copies of an init measure `ν`
on `(ℝᵈ × ℝ)`. Provides the natural probability space for LLN
applications. -/
def iidInit (d : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    Measure (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => ν)

/-- The iid init measure is a probability measure. -/
instance instIsProbabilityMeasure_iidInit
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (iidInit d ν) := by
  unfold iidInit
  infer_instance

/-! ### Strong law for the sigma-block sample average -/

/-- **Auxiliary — the k-th coordinate copy of `neuronNTK` under
`iidInit`.** For fixed inputs `x, x'` and activation `σ`, this is the
scalar-valued random variable `ω ↦ σ(⟨(ω k).1, x⟩ + (ω k).2)
· σ(⟨(ω k).1, x'⟩ + (ω k).2)`. -/
def neuronNTKCoord (σ : ℝ → ℝ)
    (x x' : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ :=
  fun ω => ProbabilityTheory.neuronNTK σ x x' (ω k)

/-- The neuron-NTK coordinate copy is measurable. -/
lemma neuronNTKCoord_measurable {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    (x x' : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    Measurable (neuronNTKCoord σ x x' k) := by
  unfold neuronNTKCoord
  exact (ProbabilityTheory.neuronNTK_measurable hσ_meas x x').comp
    (measurable_pi_apply _)

/-- The neuron-NTK coordinate copy is bounded by `σ_inf^2`. -/
lemma neuronNTKCoord_bound {σ : ℝ → ℝ} {σ_inf : ℝ}
    (hσ_nn : 0 ≤ σ_inf) (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    (x x' : EuclideanSpace ℝ (Fin d)) (k : ℕ)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) :
    |neuronNTKCoord σ x x' k ω| ≤ σ_inf * σ_inf := by
  unfold neuronNTKCoord
  exact ProbabilityTheory.neuronNTK_bound hσ_nn hσ_bdd x x' (ω k)

/-- Integrability of the neuron-NTK coordinate copy under `iidInit ν`. -/
lemma neuronNTKCoord_integrable
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {σ_inf : ℝ} (hσ_nn : 0 ≤ σ_inf) (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    (x x' : EuclideanSpace ℝ (Fin d)) (k : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    Integrable (neuronNTKCoord σ x x' k) (iidInit d ν) := by
  refine (integrable_const (σ_inf * σ_inf)).mono' ?_ ?_
  · exact (neuronNTKCoord_measurable hσ_meas x x' k).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ω => by
      have h := neuronNTKCoord_bound hσ_nn hσ_bdd x x' k ω
      simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hσ_nn hσ_nn)] using h)

/-- **Independence of the ℕ-indexed neuron-NTK coordinate family** under
`iidInit ν`. Follows from `iIndepFun_infinitePi`. -/
lemma neuronNTKCoord_iIndepFun {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    iIndepFun (neuronNTKCoord σ x x' ·) (iidInit d ν) := by
  have h_meas : ∀ _ : ℕ,
      Measurable (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
        ProbabilityTheory.neuronNTK σ x x' wb) :=
    fun _ => ProbabilityTheory.neuronNTK_measurable hσ_meas x x'
  -- Apply `iIndepFun_infinitePi` with the fixed function.
  have h := ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ => ν)
    (X := fun _ : ℕ => (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
      ProbabilityTheory.neuronNTK σ x x' wb)) h_meas
  exact h

/-- **Pairwise independence** of the ℕ-indexed neuron-NTK coordinate
family under `iidInit ν`. -/
lemma neuronNTKCoord_pairwise_indepFun
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    Pairwise ((· ⟂ᵢ[iidInit d ν] ·) on (neuronNTKCoord σ x x' ·)) := by
  intro i j hij
  exact (neuronNTKCoord_iIndepFun hσ_meas x x' ν).indepFun hij

/-- **Identical distribution of the coordinate projections** under
`iidInit ν`. Under `infinitePi (fun _ : ℕ => ν)`, evaluating at
coordinate `k` and evaluating at coordinate `0` both push forward to
`ν`. -/
lemma iidInit_coord_identDistrib
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (k : ℕ) :
    IdentDistrib (fun ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ => ω k)
      (fun ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ => ω 0)
      (iidInit d ν) (iidInit d ν) := by
  have h_eval_k_mp := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => ν) k
  have h_eval_0_mp := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => ν) 0
  refine
    { aemeasurable_fst := (measurable_pi_apply k).aemeasurable,
      aemeasurable_snd := (measurable_pi_apply 0).aemeasurable,
      map_eq := ?_ }
  unfold iidInit
  show (Measure.infinitePi (fun _ : ℕ => ν)).map (Function.eval k)
    = (Measure.infinitePi (fun _ : ℕ => ν)).map (Function.eval 0)
  rw [h_eval_k_mp.map_eq, h_eval_0_mp.map_eq]

/-- **Identical distribution** of the ℕ-indexed neuron-NTK coordinate
family under `iidInit ν`. -/
lemma neuronNTKCoord_identDistrib
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (k : ℕ) :
    IdentDistrib (neuronNTKCoord σ x x' k) (neuronNTKCoord σ x x' 0)
      (iidInit d ν) (iidInit d ν) := by
  have h_meas_pre : Measurable
      (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
        ProbabilityTheory.neuronNTK σ x x' wb) :=
    ProbabilityTheory.neuronNTK_measurable hσ_meas x x'
  -- Compose the coordinate ident-distrib with `neuronNTK σ x x'`.
  exact (iidInit_coord_identDistrib (d := d) ν k).comp h_meas_pre

/-- The expectation `𝔼_{ω ~ iidInit}[neuronNTKCoord σ x x' 0]` equals
`∫ neuronNTK σ x x' wb ∂ν`. -/
lemma neuronNTKCoord_integral_eq
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    ∫ ω, neuronNTKCoord σ x x' 0 ω ∂(iidInit d ν) =
      ∫ wb, ProbabilityTheory.neuronNTK σ x x' wb ∂ν := by
  unfold neuronNTKCoord
  have h_meas_pre : Measurable
      (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
        ProbabilityTheory.neuronNTK σ x x' wb) :=
    ProbabilityTheory.neuronNTK_measurable hσ_meas x x'
  have h_eval_mp := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => ν) 0
  -- Change of variables via the measure-preserving projection.
  calc ∫ ω, ProbabilityTheory.neuronNTK σ x x' (ω 0) ∂(iidInit d ν)
      = ∫ wb, ProbabilityTheory.neuronNTK σ x x' wb
          ∂((iidInit d ν).map (fun ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ => ω 0)) := by
        rw [integral_map (measurable_pi_apply _).aemeasurable
              h_meas_pre.aestronglyMeasurable]
    _ = ∫ wb, ProbabilityTheory.neuronNTK σ x x' wb ∂ν := by
        congr 1
        show (iidInit d ν).map (Function.eval 0) = ν
        exact h_eval_mp.map_eq

/-- **Strong law of large numbers for the sigma-block empirical NTK.**

Under the iid init measure on `ℕ → (ℝᵈ × ℝ)`, the sample average of
the single-neuron σ-block contributions converges almost surely to the
population σ-block integral:

  `∀ᵐ ω, Tendsto (fun p ↦ (1/p) Σ_{k < p} neuronNTK σ x x' (ω k))
     atTop (𝓝 (∫ neuronNTK σ x x' wb ∂ν))`.

This is the σ-block half of the JGH decomposition + LLN. Applying
`strong_law_ae_real` to the ℕ-indexed family of neuron contributions
with (a) bounded → integrable, (b) pairwise IndepFun via
`iIndepFun_infinitePi.indepFun`, (c) IdentDistrib via
`measurePreserving_eval_infinitePi`. -/
theorem neuronNTK_strong_law_ae
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {σ_inf : ℝ} (hσ_nn : 0 ≤ σ_inf) (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂(iidInit d ν),
      Tendsto
        (fun p : ℕ => (∑ k ∈ range p, neuronNTKCoord σ x x' k ω) / (p : ℝ))
        atTop
        (𝓝 (∫ wb, ProbabilityTheory.neuronNTK σ x x' wb ∂ν)) := by
  have h_int : Integrable (neuronNTKCoord σ x x' 0) (iidInit d ν) :=
    neuronNTKCoord_integrable hσ_meas hσ_nn hσ_bdd x x' 0 ν
  have h_indep : Pairwise ((· ⟂ᵢ[iidInit d ν] ·) on (neuronNTKCoord σ x x' ·)) :=
    neuronNTKCoord_pairwise_indepFun hσ_meas x x' ν
  have h_ident : ∀ k, IdentDistrib (neuronNTKCoord σ x x' k)
        (neuronNTKCoord σ x x' 0) (iidInit d ν) (iidInit d ν) :=
    fun k => neuronNTKCoord_identDistrib hσ_meas x x' ν k
  have h_sl :=
    ProbabilityTheory.strong_law_ae_real (μ := iidInit d ν)
      (neuronNTKCoord σ x x' ·) h_int h_indep h_ident
  -- Identify the expectation.
  have h_exp := neuronNTKCoord_integral_eq (d := d) hσ_meas x x' ν
  filter_upwards [h_sl] with ω hω
  rw [← h_exp]
  exact hω

/-! ### Strong law for the sigma'-block sample average -/

/-- Auxiliary — the k-th coordinate copy of `gradNeuronNTK` under
`iidInit`. -/
def gradNeuronNTKCoord (σ' : ℝ → ℝ)
    (x x' : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ :=
  fun ω => ProbabilityTheory.gradNeuronNTK σ' x x' (ω k)

/-- The grad-neuron-NTK coordinate copy is measurable. -/
lemma gradNeuronNTKCoord_measurable {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    (x x' : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    Measurable (gradNeuronNTKCoord σ' x x' k) := by
  unfold gradNeuronNTKCoord
  exact (ProbabilityTheory.gradNeuronNTK_measurable hσ'_meas x x').comp
    (measurable_pi_apply _)

/-- The grad-neuron-NTK coordinate copy is bounded by `M'^2 * G`
where `G = |⟨x, x'⟩|`. -/
lemma gradNeuronNTKCoord_bound {σ' : ℝ → ℝ} {M' G : ℝ}
    (hM' : 0 ≤ M') (hσ' : ∀ z, |σ' z| ≤ M')
    {x x' : EuclideanSpace ℝ (Fin d)} (hG : |inner ℝ x x'| ≤ G)
    (k : ℕ) (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) :
    |gradNeuronNTKCoord σ' x x' k ω| ≤ M' ^ 2 * G := by
  unfold gradNeuronNTKCoord
  exact ProbabilityTheory.gradNeuronNTK_abs_le hM' hσ' hG (ω k)

/-- Integrability of the grad-neuron-NTK coordinate copy under
`iidInit ν`. -/
lemma gradNeuronNTKCoord_integrable
    {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    {M' G : ℝ} (hM' : 0 ≤ M') (hσ' : ∀ z, |σ' z| ≤ M')
    {x x' : EuclideanSpace ℝ (Fin d)} (hG : |inner ℝ x x'| ≤ G)
    (k : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    Integrable (gradNeuronNTKCoord σ' x x' k) (iidInit d ν) := by
  refine (integrable_const (M' ^ 2 * G)).mono' ?_ ?_
  · exact (gradNeuronNTKCoord_measurable hσ'_meas x x' k).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ω => by
      have h := gradNeuronNTKCoord_bound hM' hσ' hG k ω
      have hG_nn : 0 ≤ G := le_trans (abs_nonneg _) hG
      have h_prod_nn : 0 ≤ M' ^ 2 * G := mul_nonneg (by positivity) hG_nn
      simpa [Real.norm_eq_abs, abs_of_nonneg h_prod_nn] using h)

/-- **Independence** of the ℕ-indexed grad-neuron-NTK coordinate
family under `iidInit ν`. -/
lemma gradNeuronNTKCoord_iIndepFun {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    iIndepFun (gradNeuronNTKCoord σ' x x' ·) (iidInit d ν) := by
  have h_meas : ∀ _ : ℕ,
      Measurable (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
        ProbabilityTheory.gradNeuronNTK σ' x x' wb) :=
    fun _ => ProbabilityTheory.gradNeuronNTK_measurable hσ'_meas x x'
  exact ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ => ν)
    (X := fun _ : ℕ => (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
      ProbabilityTheory.gradNeuronNTK σ' x x' wb)) h_meas

/-- Pairwise independence of the ℕ-indexed grad-neuron-NTK coordinate
family under `iidInit ν`. -/
lemma gradNeuronNTKCoord_pairwise_indepFun
    {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    Pairwise ((· ⟂ᵢ[iidInit d ν] ·) on (gradNeuronNTKCoord σ' x x' ·)) := by
  intro i j hij
  exact (gradNeuronNTKCoord_iIndepFun hσ'_meas x x' ν).indepFun hij

/-- **Identical distribution** of the ℕ-indexed grad-neuron-NTK
coordinate family under `iidInit ν`. -/
lemma gradNeuronNTKCoord_identDistrib
    {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (k : ℕ) :
    IdentDistrib (gradNeuronNTKCoord σ' x x' k) (gradNeuronNTKCoord σ' x x' 0)
      (iidInit d ν) (iidInit d ν) := by
  have h_meas_pre : Measurable
      (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
        ProbabilityTheory.gradNeuronNTK σ' x x' wb) :=
    ProbabilityTheory.gradNeuronNTK_measurable hσ'_meas x x'
  exact (iidInit_coord_identDistrib (d := d) ν k).comp h_meas_pre

/-- The expectation `𝔼_{ω ~ iidInit}[gradNeuronNTKCoord σ' x x' 0]`
equals `∫ gradNeuronNTK σ' x x' wb ∂ν`. -/
lemma gradNeuronNTKCoord_integral_eq
    {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    ∫ ω, gradNeuronNTKCoord σ' x x' 0 ω ∂(iidInit d ν) =
      ∫ wb, ProbabilityTheory.gradNeuronNTK σ' x x' wb ∂ν := by
  unfold gradNeuronNTKCoord
  have h_meas_pre : Measurable
      (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
        ProbabilityTheory.gradNeuronNTK σ' x x' wb) :=
    ProbabilityTheory.gradNeuronNTK_measurable hσ'_meas x x'
  have h_eval_mp := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => ν) 0
  calc ∫ ω, ProbabilityTheory.gradNeuronNTK σ' x x' (ω 0) ∂(iidInit d ν)
      = ∫ wb, ProbabilityTheory.gradNeuronNTK σ' x x' wb
          ∂((iidInit d ν).map (fun ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ => ω 0)) := by
        rw [integral_map (measurable_pi_apply _).aemeasurable
              h_meas_pre.aestronglyMeasurable]
    _ = ∫ wb, ProbabilityTheory.gradNeuronNTK σ' x x' wb ∂ν := by
        congr 1
        show (iidInit d ν).map (Function.eval 0) = ν
        exact h_eval_mp.map_eq

/-- **Strong law of large numbers for the sigma'-block empirical NTK.**

Under the iid init measure on `ℕ → (ℝᵈ × ℝ)`, the sample average of
the single-neuron σ'-block contributions converges almost surely to
the population σ'-block integral. This is the σ'-block half of the
JGH decomposition + LLN. -/
theorem gradNeuronNTK_strong_law_ae
    {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    {M' G : ℝ} (hM' : 0 ≤ M') (hσ' : ∀ z, |σ' z| ≤ M')
    {x x' : EuclideanSpace ℝ (Fin d)} (hG : |inner ℝ x x'| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂(iidInit d ν),
      Tendsto
        (fun p : ℕ => (∑ k ∈ range p, gradNeuronNTKCoord σ' x x' k ω) / (p : ℝ))
        atTop
        (𝓝 (∫ wb, ProbabilityTheory.gradNeuronNTK σ' x x' wb ∂ν)) := by
  have h_int : Integrable (gradNeuronNTKCoord σ' x x' 0) (iidInit d ν) :=
    gradNeuronNTKCoord_integrable hσ'_meas hM' hσ' hG 0 ν
  have h_indep : Pairwise ((· ⟂ᵢ[iidInit d ν] ·) on (gradNeuronNTKCoord σ' x x' ·)) :=
    gradNeuronNTKCoord_pairwise_indepFun hσ'_meas x x' ν
  have h_ident : ∀ k, IdentDistrib (gradNeuronNTKCoord σ' x x' k)
        (gradNeuronNTKCoord σ' x x' 0) (iidInit d ν) (iidInit d ν) :=
    fun k => gradNeuronNTKCoord_identDistrib hσ'_meas x x' ν k
  have h_sl :=
    ProbabilityTheory.strong_law_ae_real (μ := iidInit d ν)
      (gradNeuronNTKCoord σ' x x' ·) h_int h_indep h_ident
  have h_exp := gradNeuronNTKCoord_integral_eq (d := d) hσ'_meas x x' ν
  filter_upwards [h_sl] with ω hω
  rw [← h_exp]
  exact hω

/-! ### Main theorem: JGH decomposition + LLN -/

/-- **T5a-L4: JGH decomposition + LLN.**

For any bounded measurable activation `σ` (with `|σ z| ≤ σ_inf`), any
bounded measurable derivative `σ'` (with `|σ' z| ≤ M'`), and any inputs
`x, x' ∈ ℝᵈ` with a data-Gram envelope `|⟨x, x'⟩| ≤ G`, the width-`p`
empirical NTK entry at `(x, x')` — summing the σ-block and σ'-block
per-neuron contributions — converges almost surely (under the iid init
measure `iidInit d ν`) to the population NTK entry:

  `∀ᵐ ω, Tendsto (fun p ↦ (1/p) Σ_{k < p}
      [neuronNTK σ x x' (ω k) + gradNeuronNTK σ' x x' (ω k)])
    atTop (𝓝 (∫ neuronNTK σ x x' wb ∂ν + ∫ gradNeuronNTK σ' x x' wb ∂ν))`.

This is the two-layer JGH-2018 §3.1 decomposition + LLN limit, stated
in `LTFP.MathlibExt.Probability` form (`neuronNTK` + `gradNeuronNTK`
match Bach's Eq. 12.29 σ- and σ'-blocks respectively).

The theorem is activation-agnostic: it does not restrict to ReLU. The
closed-form ReLU NTK integral (Cho–Saul 2009 §3) comes later in
T5a-L3 by evaluating `∫ neuronNTK` and `∫ gradNeuronNTK` in the ReLU
case with `ν = stdMultivariateGaussian d × standardGaussianReal`. -/
theorem empiricalFullNTK_scalar_strong_law_ae
    {σ σ' : ℝ → ℝ}
    (hσ_meas : Measurable σ) (hσ'_meas : Measurable σ')
    {σ_inf M' G : ℝ}
    (hσ_nn : 0 ≤ σ_inf) (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    (hM' : 0 ≤ M') (hσ' : ∀ z, |σ' z| ≤ M')
    {x x' : EuclideanSpace ℝ (Fin d)} (hG : |inner ℝ x x'| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂(iidInit d ν),
      Tendsto
        (fun p : ℕ => (∑ k ∈ range p,
            (neuronNTKCoord σ x x' k ω + gradNeuronNTKCoord σ' x x' k ω))
              / (p : ℝ))
        atTop
        (𝓝 ((∫ wb, ProbabilityTheory.neuronNTK σ x x' wb ∂ν)
              + ∫ wb, ProbabilityTheory.gradNeuronNTK σ' x x' wb ∂ν)) := by
  have h_sigma := neuronNTK_strong_law_ae (d := d) hσ_meas hσ_nn hσ_bdd x x' ν
  have h_grad := gradNeuronNTK_strong_law_ae (d := d) hσ'_meas hM' hσ' hG ν
  filter_upwards [h_sigma, h_grad] with ω hω_σ hω_σ'
  -- The sum's average is the sum of the averages, and the limit of the
  -- sum of two convergent sequences is the sum of the limits.
  have h_split : ∀ p : ℕ,
      (∑ k ∈ range p,
        (neuronNTKCoord σ x x' k ω + gradNeuronNTKCoord σ' x x' k ω))
          / (p : ℝ)
        = (∑ k ∈ range p, neuronNTKCoord σ x x' k ω) / (p : ℝ)
        + (∑ k ∈ range p, gradNeuronNTKCoord σ' x x' k ω) / (p : ℝ) := by
    intro p
    rw [Finset.sum_add_distrib, add_div]
  simp only [h_split]
  exact hω_σ.add hω_σ'

end LTFP.MathlibExt.Probability
