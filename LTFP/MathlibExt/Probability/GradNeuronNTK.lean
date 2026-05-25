/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import LTFP.MathlibExt.Probability.NTKConcentration
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Gradient-block (`σ'`) NTK kernel definitions and entrywise bounds

**R4 NTK Part E1a** (atomic step in the σ' extension of the σ-block
random-feature NTK Bernstein concentration, parts A–D in
`LTFP/MathlibExt/Probability/NTKConcentration*.lean`).

Setting: a one-hidden-layer neural network with width `m`, iid init
`(w_j, b_j) ~ ν`, and a bounded derivative `σ' : ℝ → ℝ` with
`|σ' z| ≤ M'`. For a fixed finite input set
`xs : Fin n → EuclideanSpace ℝ (Fin d)`, the gradient-block NTK on
the points `(xs a, xs b)` is

  `K̂_m^(grad)(a, b) := (1 / m) Σ_{j=1..m} G_j^(grad)(a, b)`,
  `G_j^(grad)(a, b) := σ'(⟨w_j, xs a⟩ + b_j) · σ'(⟨w_j, xs b⟩ + b_j) · ⟨xs a, xs b⟩`,

and the **population gradient-block NTK** is `K^(grad)(a, b) :=
E G_j^(grad)(a, b)`. The `⟨xs a, xs b⟩` factor depends on the DATA pair
`(a, b)`, making this a Hadamard product with the data Gram matrix
(NOT a scalar multiple of the σ-block).

This file lands the **scalar layer** of the gradient-block extension:
single-neuron definitions, empirical and population matrix entries,
the entrywise pointwise bound, the data-symmetry equality, and
measurability. The independence / sub-Gaussian / matrix Bernstein
machinery for the gradient block is the next atomic step (E1b),
following the same template as the σ-block in
`NTKConcentration.lean`.

## Main definitions

* `gradNeuronNTK` — single-neuron gradient-block NTK contribution
  `σ'(⟨w,x⟩+b) · σ'(⟨w,x'⟩+b) · ⟨x, x'⟩`.
* `empiricalGradNTK` — width-`m` empirical gradient-block NTK matrix
  entry `(a, b)`.
* `populationGradNTK` — population gradient-block NTK matrix entry
  `(a, b)` (integral under the init measure).

## Main results

* `gradNeuronNTK_abs_le` — pointwise bound
  `|gradNeuronNTK σ' x x' wb| ≤ M' ^ 2 * G` whenever
  `|σ' z| ≤ M'` and `|⟨x, x'⟩| ≤ G`.
* `gradNeuronNTK_symm` — data symmetry
  `gradNeuronNTK σ' x x' wb = gradNeuronNTK σ' x' x wb`, since the
  real inner product is symmetric and the two `σ'` factors swap.
* `gradNeuronNTK_measurable` — measurability of the single-neuron
  gradient-block NTK as a function of `(w, b)`, parallel to
  `neuronNTK_measurable`.
-/

namespace ProbabilityTheory

open MeasureTheory NNReal Real BigOperators

variable {d : ℕ}

/-- **Single-neuron gradient-block (σ') NTK contribution.**

Given a bounded derivative `σ' : ℝ → ℝ`, inputs `x, x' ∈ ℝᵈ`, and a
weight-bias pair `wb = (w, b)`, the single-neuron gradient-block NTK
contribution is
`σ'(⟨w, x⟩ + b) · σ'(⟨w, x'⟩ + b) · ⟨x, x'⟩`.

The trailing `⟨x, x'⟩` factor encodes the data-Gram-Hadamard structure
of the gradient block in Bach's Eq. 12.29. -/
noncomputable def gradNeuronNTK (σ' : ℝ → ℝ)
    (x x' : EuclideanSpace ℝ (Fin d))
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  σ' (inner ℝ wb.1 x + wb.2) *
  σ' (inner ℝ wb.1 x' + wb.2) *
  inner ℝ x x'

/-- **Width-`m` empirical gradient-block NTK matrix entry** at `(a, b)`.

Given an iid sample `ω : Fin m → (ℝᵈ × ℝ)` of weight-bias pairs,
the empirical gradient-block NTK at the pair `(xs a, xs b)` is the
sample average `(1/m) Σⱼ gradNeuronNTK σ' (xs a) (xs b) (ω j)`. -/
noncomputable def empiricalGradNTK (σ' : ℝ → ℝ) {n : ℕ}
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) {m : ℕ}
    (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun a b => (1 / (m : ℝ)) * ∑ j, gradNeuronNTK σ' (xs a) (xs b) (ω j)

/-- **Population gradient-block NTK matrix entry** at `(a, b)`.

Given an init measure `ν` on `(ℝᵈ × ℝ)`, the population gradient-block
NTK at the pair `(xs a, xs b)` is `E_{wb ~ ν} gradNeuronNTK σ' (xs a)
(xs b) wb`. -/
noncomputable def populationGradNTK (σ' : ℝ → ℝ) {n : ℕ}
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun a b => ∫ wb, gradNeuronNTK σ' (xs a) (xs b) wb ∂ν

/-! ### Boundedness, symmetry, and measurability -/

/-- **Pointwise entrywise bound on the single-neuron gradient-block NTK.**

For a bounded derivative `|σ' z| ≤ M'` and a data-Gram envelope
`|⟨x, x'⟩| ≤ G`, the gradient-block contribution at any `wb` satisfies
`|gradNeuronNTK σ' x x' wb| ≤ M' ^ 2 * G`.

This is the gradient-block analogue of `neuronNTK_bound`. Callers
typically supply `G := X_max ^ 2` via Cauchy–Schwarz when
`‖x_i‖ ≤ X_max` for all data points. -/
theorem gradNeuronNTK_abs_le {σ' : ℝ → ℝ} {M' G : ℝ}
    (hM' : 0 ≤ M') (hσ' : ∀ z, |σ' z| ≤ M')
    {x x' : EuclideanSpace ℝ (Fin d)} (hG : |inner ℝ x x'| ≤ G)
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    |gradNeuronNTK σ' x x' wb| ≤ M' ^ 2 * G := by
  unfold gradNeuronNTK
  -- |a * b * c| = |a| * |b| * |c|.
  rw [abs_mul, abs_mul]
  -- Bound the σ' · σ' prefix by M' · M' = M'^2 (nonneg, monotone in c).
  have h_prefix : |σ' (inner ℝ wb.1 x + wb.2)| *
      |σ' (inner ℝ wb.1 x' + wb.2)| ≤ M' * M' :=
    mul_le_mul (hσ' _) (hσ' _) (abs_nonneg _) hM'
  -- 0 ≤ G follows from |⟨x,x'⟩| ≤ G and 0 ≤ |⟨x,x'⟩|.
  have hG_nn : 0 ≤ G := le_trans (abs_nonneg _) hG
  -- Combine into one bound (mul_le_mul: h₁ h₂ c0 b0 ⊢ a·c ≤ b·d).
  have h_combine : |σ' (inner ℝ wb.1 x + wb.2)| *
        |σ' (inner ℝ wb.1 x' + wb.2)| *
        |inner ℝ x x'| ≤ (M' * M') * G :=
    mul_le_mul h_prefix hG (abs_nonneg _) (mul_nonneg hM' hM')
  -- Rewrite M' * M' as M' ^ 2.
  have h_sq : M' * M' = M' ^ 2 := by ring
  rw [h_sq] at h_combine
  exact h_combine

/-- **Data symmetry of the single-neuron gradient-block NTK.**

Swapping the two data points `x ↔ x'` leaves the gradient-block
contribution unchanged: the two `σ'` factors swap (commutativity of
multiplication) and the real inner product is symmetric, so
`⟨x, x'⟩ = ⟨x', x⟩`. -/
theorem gradNeuronNTK_symm (σ' : ℝ → ℝ)
    (x x' : EuclideanSpace ℝ (Fin d))
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    gradNeuronNTK σ' x x' wb = gradNeuronNTK σ' x' x wb := by
  unfold gradNeuronNTK
  -- Inner product symmetry (REAL inner product): ⟨x, x'⟩ = ⟨x', x⟩.
  have h_inner : (inner ℝ x x' : ℝ) = inner ℝ x' x := real_inner_comm x' x
  rw [h_inner]
  -- Now the two σ' factors swap by commutativity of `*`.
  ring

/-- **Measurability of the single-neuron gradient-block NTK.** If
`σ'` is measurable, then `wb ↦ gradNeuronNTK σ' x x' wb` is
measurable.

The proof mirrors `neuronNTK_measurable`: the `wb`-dependence is
through `σ'(inner ℝ wb.1 x + wb.2)` and `σ'(inner ℝ wb.1 x' + wb.2)`;
the trailing `inner ℝ x x'` factor is a `wb`-constant. -/
theorem gradNeuronNTK_measurable {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    (x x' : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
      gradNeuronNTK σ' x x' wb) := by
  unfold gradNeuronNTK
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
  -- The trailing `inner ℝ x x'` factor is a `wb`-constant.
  exact ((hσ'_meas.comp h_pre_x).mul (hσ'_meas.comp h_pre_x')).mul_const _

end ProbabilityTheory
