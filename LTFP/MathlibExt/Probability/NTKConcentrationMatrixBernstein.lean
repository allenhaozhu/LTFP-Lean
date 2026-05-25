/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKMatrixSummand
import LTFP.MathlibExt.MatrixAnalysis.MatrixBernsteinOpNorm
import LTFP.MathlibExt.MatrixAnalysis.HermitianSqLeNormSqOne
import LTFP.MathlibExt.MatrixAnalysis.MapOfRealNorm
import LTFP.Ch01_Preliminaries.Concentration
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.Instances.Matrix

/-!
# Sharp empirical-NTK matrix Bernstein concentration

**R4 Part D — final assembly.** This file combines

* the sum identity `sum_centeredNeuronNTKSummand_eq_deviation`
  (Part A, `NTKMatrixSummand.lean`),
* the per-summand bounds — Hermitian, op-norm, entrywise centering,
  norm-form variance bound (Part C, `NTKMatrixSummand.lean`),
* the operator-norm matrix Bernstein bound `Matrix.bernstein_op_norm_full`
  (Part B, `MatrixBernsteinOpNorm.lean`),
* the norm-to-Loewner bridge for PSD matrices
  `Matrix.PosSemidef.le_norm_smul_one_of_isHermitian`
  (Part C.5, `HermitianSqLeNormSqOne.lean`),

into a sharp Bernstein-style concentration inequality for the
empirical-minus-population NTK deviation matrix.

## Main results

* `ProbabilityTheory.empiricalNTK_matrix_bernstein` — for a bounded
  measurable activation `|σ z| ≤ M`, an iid sample of size `m` from a
  probability measure `ν`, and any radius `t > 0`,

    `P(t ≤ ‖(empiricalNTK σ xs ω - populationNTK σ xs ν).map ofReal‖)`
      `≤ 2 · matrix_bernstein_bound n t (4 n² M⁴ / m) (2 n M² / m)`.

  The variance proxy `σ² := 4 n² M⁴ / m` and per-summand radius
  `R := 2 n M² / m` are precisely the constants delivered by Part C
  (`centeredNeuronNTKSummand_opNorm_le` and the norm-form variance
  bound).

## Proof outline

For each `j : Fin m`, set
`X j ω := centeredNeuronNTKSummand σ xs ν m ω`. Note that `X j` does not
actually depend on `j` (the family is iid), so the sample is fed into
`X` via the projection `ω j` of `ω : Fin m → ℝᵈ × ℝ`. The product
measure `Measure.pi (fun _ : Fin m => ν)` makes the family `iIndepFun`,
giving Bernstein's independence hypothesis.

The four matrix-Bernstein side conditions are discharged as follows:

* **Hermitian** — `centeredNeuronNTKSummand_isHermitian` (Part C).
* **Bounded** — `centeredNeuronNTKSummand_opNorm_le` with `R := 2 n M²/m`.
* **Centered** — lift entrywise `apply_integral_eq_zero` (Part C) to
  the matrix-valued integral via `ContinuousLinearMap.integral_comp_comm`
  applied to the entry CLM. This is sub-helper
  `centeredNeuronNTKSummand_integral_eq_zero`.
* **Variance (Loewner)** — for Hermitian `X`, `X * X` is PSD pointwise;
  hence `∫ X · X ∂ν` is PSD (sub-helper `posSemidef_of_integral`); the
  sum across `j` (where the family is iid) is `m · ∫ X · X ∂ν`, which is
  PSD; the operator-norm bound from Part C combined with the
  norm-to-Loewner bridge from Part C.5 yields the Loewner bound
  `∑ ∫ X · X ≤ σ² · 1`.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. 12 (2012), Corollary 6.1.2.
* F. Bach, *Learning Theory from First Principles* (2024), §12.4.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ProbabilityTheory

open MeasureTheory BigOperators Matrix

variable {d : ℕ}

/-! ### Sub-helper D1: matrix-valued centering -/

/-- The entry-extraction map as a continuous linear map.

`Matrix.entryLinearMap` exposes `M ↦ M i j` as a `LinearMap`. Because
`Matrix (Fin n) (Fin n) ℂ` is a finite-dimensional ℂ-module, every
linear map from it is continuous. We use this to lift entrywise
identities of integrals to matrix-valued integral identities via
`ContinuousLinearMap.integral_comp_comm`. -/
noncomputable def entryCLM (n : ℕ) (i j : Fin n) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)

@[simp] lemma entryCLM_apply (n : ℕ) (i j : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) :
    entryCLM n i j M = M i j := rfl

/-! ### Strong measurability of the matrix-valued centered NTK summand

We need `AEStronglyMeasurable` of `wb ↦ centeredNeuronNTKSummand σ xs ν m wb`.
We build this from a sum-of-single-basis decomposition, where each
summand `single i j (scalar_meas wb)` is AE-strongly-measurable.
-/

/-- AE-strong measurability of the scalar `(neuronNTK σ x x' wb : ℂ)`. -/
lemma neuronNTK_complex_aestronglyMeasurable
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    AEStronglyMeasurable
      (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
        ((neuronNTK σ x x' wb : ℝ) : ℂ)) ν :=
  (Complex.continuous_ofReal.measurable.comp
    (neuronNTK_measurable hσ_meas x x')).aestronglyMeasurable

/-- AE-strong measurability of `wb ↦ Matrix.single i j (g wb)` from
AE-strong measurability of `g`. Used as a building block for matrix-valued
AE-strong measurability by decomposing a matrix into its single-entry
basis. -/
lemma _root_.Matrix.aestronglyMeasurable_single
    {n : ℕ} {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    {μ : Measure Ω} (i j : Fin n) {g : Ω → ℂ}
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun ω => Matrix.single i j (g ω)) μ := by
  have h_cont : Continuous (fun c : ℂ => Matrix.single (n := Fin n) (m := Fin n) i j c) := by
    refine continuous_pi (fun i' => continuous_pi (fun j' => ?_))
    by_cases h : i = i' ∧ j = j'
    · simpa [Matrix.single_apply, h] using continuous_id
    · simpa [Matrix.single_apply, h] using continuous_const
  exact h_cont.comp_aestronglyMeasurable hg

/-- AE-strong measurability of the matrix-valued single-neuron NTK
contribution. -/
lemma neuronNTKMatrixC_aestronglyMeasurable
    {n : ℕ} {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    AEStronglyMeasurable (fun wb => neuronNTKMatrixC σ xs wb) ν := by
  -- Decompose `M = ∑ i, ∑ j, single i j (M i j)`.
  have h_decomp : (fun wb => neuronNTKMatrixC σ xs wb)
      = (fun wb => ∑ i, ∑ j,
          Matrix.single i j ((neuronNTK σ (xs i) (xs j) wb : ℝ) : ℂ)) := by
    funext wb
    rw [show neuronNTKMatrixC σ xs wb
          = ∑ i, ∑ j, Matrix.single i j (neuronNTKMatrixC σ xs wb i j) from
        Matrix.matrix_eq_sum_single (neuronNTKMatrixC σ xs wb)]
    rfl
  rw [h_decomp]
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun j _ => ?_)
  exact Matrix.aestronglyMeasurable_single i j
    (neuronNTK_complex_aestronglyMeasurable hσ_meas (xs i) (xs j) ν)

/-- AE-strong measurability of the matrix-valued centered NTK summand. -/
lemma centeredNeuronNTKSummand_aestronglyMeasurable
    {n m : ℕ} {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    AEStronglyMeasurable (fun wb => centeredNeuronNTKSummand σ xs ν m wb) ν := by
  unfold centeredNeuronNTKSummand
  -- Continuity of `fun A => (1/m) • A` on Matrix → Matrix.
  have h_cont_smul : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
      (1 / (m : ℝ)) • A) := continuous_const.smul continuous_id
  have h_diff : AEStronglyMeasurable
      (fun wb => neuronNTKMatrixC σ xs wb -
        (populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ))) ν := by
    refine AEStronglyMeasurable.sub
      (neuronNTKMatrixC_aestronglyMeasurable hσ_meas xs ν)
      aestronglyMeasurable_const
  exact h_cont_smul.comp_aestronglyMeasurable h_diff

/-- Integrability of the matrix-valued centered NTK summand. -/
lemma centeredNeuronNTKSummand_integrable
    {n m : ℕ} {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    Integrable (fun wb => centeredNeuronNTKSummand σ xs ν m wb) ν := by
  refine Integrable.mono' (g := fun _ => 2 * (n : ℝ) * M ^ 2 / (m : ℝ))
    (integrable_const _)
    (centeredNeuronNTKSummand_aestronglyMeasurable hσ_meas xs ν) ?_
  refine Filter.Eventually.of_forall (fun wb => ?_)
  have h := centeredNeuronNTKSummand_opNorm_le hM hσ xs ν hm wb
  have h_nn : 0 ≤ 2 * (n : ℝ) * M ^ 2 / (m : ℝ) := by
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    positivity
  -- The Integrable.mono' hypothesis takes the form `‖f a‖ ≤ g a`.
  -- Here `g a = 2 * n * M^2 / m`. Goal is `‖center ...‖ ≤ (fun _ => 2*n*M^2/m) wb`,
  -- which beta-reduces to `‖center ...‖ ≤ 2*n*M^2/m`. Note that `g` is real;
  -- the bound `h` is `‖center‖ ≤ 2 n M² / m`, which suffices.
  exact h

/-- **Sub-helper D1.** Matrix-valued centering: the integral of the
centered scaled NTK summand is the zero matrix.

Lifted from the entrywise zero identity
`centeredNeuronNTKSummand_apply_integral_eq_zero` (Part C) via the
entry CLM and `ContinuousLinearMap.integral_comp_comm`. -/
lemma centeredNeuronNTKSummand_integral_eq_zero
    {n m : ℕ} {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    ∫ wb, centeredNeuronNTKSummand σ xs ν m wb ∂ν
      = (0 : Matrix (Fin n) (Fin n) ℂ) := by
  refine Matrix.ext (fun i j => ?_)
  have h_int : Integrable
      (fun wb => centeredNeuronNTKSummand σ xs ν m wb) ν :=
    centeredNeuronNTKSummand_integrable hσ_meas hM hσ xs ν hm
  -- `(∫ X) i j = ∫ (X wb) i j ∂ν` via the entry CLM.
  have h_swap :=
    (ContinuousLinearMap.integral_comp_comm (entryCLM n i j) h_int)
  simp only [entryCLM_apply] at h_swap
  -- The RHS integrand is the (i, j) entry, integrating to 0 by Part C.
  have h_zero := centeredNeuronNTKSummand_apply_integral_eq_zero
    hσ_meas hM hσ xs ν hm i j
  show (∫ wb, centeredNeuronNTKSummand σ xs ν m wb ∂ν) i j
      = (0 : Matrix (Fin n) (Fin n) ℂ) i j
  rw [Matrix.zero_apply, ← h_swap, h_zero]

/-! ### Sub-helper D2: Loewner-form variance bound -/

/-- For Hermitian `H : Matrix (Fin n) (Fin n) ℂ`, the product `H * H`
is positive-semidefinite. -/
lemma _root_.Matrix.IsHermitian.mul_self_posSemidef
    {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) :
    (H * H).PosSemidef := by
  -- `H * H = Hᴴ * H` (since `Hᴴ = H` for Hermitian `H`), which is PSD.
  have h_eq : H * H = Hᴴ * H := by rw [hH.eq]
  rw [h_eq]
  exact Matrix.posSemidef_conjTranspose_mul_self H

/-- The bilinear form `M ↦ star x ⬝ᵥ (M *ᵥ x)` is a continuous linear
map `Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ`. Used to lift the dot-product
positivity in the definition of `PosSemidef` through Bochner integrals. -/
noncomputable def quadFormCLM (n : ℕ) (x : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  ∑ i, ∑ j, (star (x i) * x j) • entryCLM n i j

@[simp] lemma quadFormCLM_apply (n : ℕ) (x : Fin n → ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    quadFormCLM n x M = star x ⬝ᵥ (M *ᵥ x) := by
  unfold quadFormCLM
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    entryCLM_apply, smul_eq_mul]
  -- `star x ⬝ᵥ (M *ᵥ x) = ∑ i, (star x) i * (M *ᵥ x) i
  --                    = ∑ i, star (x i) * ∑ j, M i j * x j
  --                    = ∑ i, ∑ j, star (x i) * (M i j * x j)
  --                    = ∑ i, ∑ j, (star (x i) * x j) * M i j`.
  simp only [dotProduct, mulVec, dotProduct, Pi.star_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **PSD-of-integral.** The Bochner integral of a pointwise PSD-valued
function (with star-symmetric Hermitian-ness) is positive-semidefinite. -/
lemma _root_.Matrix.posSemidef_of_integral
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Matrix (Fin n) (Fin n) ℂ)
    (hf_int : Integrable f μ)
    (hf_psd : ∀ ω, (f ω).PosSemidef) :
    (∫ ω, f ω ∂μ).PosSemidef := by
  -- Use the equivalent dot-product characterization.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian: `(∫ f)ᴴ = ∫ fᴴ`. Lift entrywise via star-conjugation
    -- of each entry.
    refine Matrix.IsHermitian.ext (fun i j => ?_)
    -- `star ((∫ f) j i) = (∫ f) i j`.
    -- Entry `(∫ f) j i = ∫ (f ω) j i ∂μ` via entry CLM.
    have h_ji : (∫ ω, f ω ∂μ) j i = ∫ ω, (f ω) j i ∂μ := by
      have h_swap :=
        (ContinuousLinearMap.integral_comp_comm (entryCLM n j i) hf_int)
      simp only [entryCLM_apply] at h_swap
      exact h_swap.symm
    have h_ij : (∫ ω, f ω ∂μ) i j = ∫ ω, (f ω) i j ∂μ := by
      have h_swap :=
        (ContinuousLinearMap.integral_comp_comm (entryCLM n i j) hf_int)
      simp only [entryCLM_apply] at h_swap
      exact h_swap.symm
    rw [h_ji, h_ij]
    -- Star (conjugation) on ℂ commutes with integral.
    have h_conj :
        star (∫ ω, (f ω) j i ∂μ) = ∫ ω, star ((f ω) j i) ∂μ := by
      have h := integral_conj (μ := μ) (f := fun ω => (f ω) j i)
      -- `integral_conj` gives `∫ conj f = conj ∫ f`; we want the symmetric.
      simpa [Complex.star_def] using h.symm
    rw [h_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    -- Pointwise hermitianness gives `star ((f ω) j i) = (f ω) i j`.
    have hH := (hf_psd ω).isHermitian
    -- `IsHermitian` says `fᴴ = f`, i.e., `(fᴴ) i j = f i j` for all i, j.
    -- The (i, j) entry of `fᴴ` is `star (f j i)`. So `star (f j i) = f i j`.
    have h_entry : star ((f ω) j i) = (f ω) i j := by
      have h_HΛ : (f ω)ᴴ i j = (f ω) i j := by
        rw [hH]
      -- `(f ω)ᴴ i j = star ((f ω) j i)`.
      rw [Matrix.conjTranspose_apply] at h_HΛ
      exact h_HΛ
    exact h_entry
  · -- `0 ≤ star x ⬝ᵥ ((∫ f) *ᵥ x)` for all `x`. Lift via the quad-form CLM.
    intro x
    have h_quad : star x ⬝ᵥ ((∫ ω, f ω ∂μ) *ᵥ x)
        = quadFormCLM n x (∫ ω, f ω ∂μ) :=
      (quadFormCLM_apply n x _).symm
    rw [h_quad]
    have h_swap :=
      (ContinuousLinearMap.integral_comp_comm (quadFormCLM n x) hf_int)
    rw [← h_swap]
    -- Pointwise nonnegativity of the integrand.
    have h_pt : ∀ ω, 0 ≤ quadFormCLM n x (f ω) := fun ω => by
      rw [quadFormCLM_apply]
      exact (hf_psd ω).dotProduct_mulVec_nonneg x
    -- Integral of pointwise nonneg ℂ-valued function is nonneg in ComplexOrder.
    have h_integrand_real : ∀ ω, (quadFormCLM n x (f ω)).im = 0 := by
      intro ω
      have h := h_pt ω
      exact (Complex.le_def.mp h).2.symm
    have h_integrand_re_nn : ∀ ω, 0 ≤ (quadFormCLM n x (f ω)).re := by
      intro ω
      have h := h_pt ω
      exact (Complex.le_def.mp h).1
    -- Integrability of `quadFormCLM n x ∘ f` follows from continuity of the CLM.
    have h_qf_int : Integrable (fun ω => quadFormCLM n x (f ω)) μ :=
      (quadFormCLM n x).integrable_comp hf_int
    have h_re_int :
        (∫ ω, quadFormCLM n x (f ω) ∂μ).re
          = ∫ ω, (quadFormCLM n x (f ω)).re ∂μ :=
      (integral_re h_qf_int).symm
    have h_im_int :
        (∫ ω, quadFormCLM n x (f ω) ∂μ).im
          = ∫ ω, (quadFormCLM n x (f ω)).im ∂μ :=
      (integral_im h_qf_int).symm
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · simp only [Complex.zero_re]
      rw [h_re_int]
      exact integral_nonneg (fun ω => h_integrand_re_nn ω)
    · simp only [Complex.zero_im]
      rw [h_im_int]
      have h_ae : ∀ᵐ ω ∂μ, (quadFormCLM n x (f ω)).im = (0 : ℝ) :=
        Filter.Eventually.of_forall h_integrand_real
      rw [integral_congr_ae h_ae, integral_zero]

/-! ### Sub-helper D2 (cont'd): Loewner-form variance bound

We assemble the Loewner-form variance hypothesis required by
`Matrix.bernstein_op_norm_full`. -/

/-- AE-strong measurability of `X · X` for the centered NTK summand. -/
lemma centeredNeuronNTKSummand_mul_self_aestronglyMeasurable
    {n m : ℕ} {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    AEStronglyMeasurable
      (fun wb => centeredNeuronNTKSummand σ xs ν m wb *
        centeredNeuronNTKSummand σ xs ν m wb) ν := by
  have h_meas := centeredNeuronNTKSummand_aestronglyMeasurable
    (m := m) hσ_meas xs ν
  exact h_meas.mul h_meas

/-- Integrability of `X · X` for the centered NTK summand. -/
lemma centeredNeuronNTKSummand_mul_self_integrable
    {n m : ℕ} {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    Integrable (fun wb =>
      centeredNeuronNTKSummand σ xs ν m wb *
        centeredNeuronNTKSummand σ xs ν m wb) ν := by
  refine Integrable.mono' (g := fun _ => 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2)
    (integrable_const _)
    (centeredNeuronNTKSummand_mul_self_aestronglyMeasurable hσ_meas xs ν)
    (Filter.Eventually.of_forall (fun wb =>
      centeredNeuronNTKSummand_mul_self_opNorm_le hM hσ xs ν hm wb))

/-- Operator-norm bound on the per-summand expected matrix product
`∫ X·X ∂ν`, derived by integrating the pointwise bound from Part C
(`centeredNeuronNTKSummand_mul_self_opNorm_le`). -/
lemma centeredNeuronNTKSummand_mul_self_integral_norm_le
    {n m : ℕ} {σ : ℝ → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    ‖∫ wb, centeredNeuronNTKSummand σ xs ν m wb *
              centeredNeuronNTKSummand σ xs ν m wb ∂ν‖
      ≤ 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2 := by
  have h_mul_pt : ∀ wb,
      ‖centeredNeuronNTKSummand σ xs ν m wb *
        centeredNeuronNTKSummand σ xs ν m wb‖
        ≤ 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2 :=
    fun wb => centeredNeuronNTKSummand_mul_self_opNorm_le hM hσ xs ν hm wb
  -- `‖∫ X·X‖ ≤ ∫ ‖X·X‖ ≤ R²·1 = R²`.
  have h_norm_le : ‖∫ wb, centeredNeuronNTKSummand σ xs ν m wb *
                        centeredNeuronNTKSummand σ xs ν m wb ∂ν‖
      ≤ ∫ wb, ‖centeredNeuronNTKSummand σ xs ν m wb *
                centeredNeuronNTKSummand σ xs ν m wb‖ ∂ν :=
    norm_integral_le_integral_norm _
  have h_int_bound : ∫ wb, ‖centeredNeuronNTKSummand σ xs ν m wb *
                            centeredNeuronNTKSummand σ xs ν m wb‖ ∂ν
      ≤ 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2 := by
    have hle :
        ∫ wb, ‖centeredNeuronNTKSummand σ xs ν m wb *
                centeredNeuronNTKSummand σ xs ν m wb‖ ∂ν
        ≤ ∫ _wb : EuclideanSpace ℝ (Fin d) × ℝ,
              4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2 ∂ν := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (integrable_const _)
        (Filter.Eventually.of_forall (fun wb => h_mul_pt wb))
    calc ∫ wb, ‖centeredNeuronNTKSummand σ xs ν m wb *
                  centeredNeuronNTKSummand σ xs ν m wb‖ ∂ν
        ≤ ∫ _wb : EuclideanSpace ℝ (Fin d) × ℝ,
              4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2 ∂ν := hle
      _ = 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2 := by
          simp [integral_const, probReal_univ]
  exact h_norm_le.trans h_int_bound

/-- PSD-ness of the integral `∫ X·X ∂ν` for the centered NTK summand. -/
lemma centeredNeuronNTKSummand_mul_self_integral_posSemidef
    {n m : ℕ} {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    (∫ wb, centeredNeuronNTKSummand σ xs ν m wb *
              centeredNeuronNTKSummand σ xs ν m wb ∂ν).PosSemidef := by
  refine Matrix.posSemidef_of_integral ν _
    (centeredNeuronNTKSummand_mul_self_integrable hσ_meas hM hσ xs ν hm)
    (fun wb => ?_)
  exact (centeredNeuronNTKSummand_isHermitian σ xs ν wb).mul_self_posSemidef

/-- Real-scalar smul of identity matrix is PSD when the scalar is nonneg. -/
lemma _root_.Matrix.posSemidef_real_smul_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {a : ℝ} (ha : 0 ≤ a) :
    ((a : ℝ) • (1 : Matrix n n ℂ)).PosSemidef := by
  -- `a • 1 = diagonal (fun _ => a)` (as a real-scalar of the identity).
  -- Goal: show this matrix is PSD.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian: it's diagonal real entries, hence its own conjugate transpose.
    refine Matrix.IsHermitian.ext (fun i j => ?_)
    by_cases hij : i = j
    · subst hij
      show star (((a : ℝ) • (1 : Matrix n n ℂ)) i i)
          = ((a : ℝ) • (1 : Matrix n n ℂ)) i i
      simp [Matrix.smul_apply, Complex.real_smul]
    · show star (((a : ℝ) • (1 : Matrix n n ℂ)) j i)
          = ((a : ℝ) • (1 : Matrix n n ℂ)) i j
      simp [Matrix.smul_apply, hij, Ne.symm hij]
  · intro x
    -- `star x ⬝ᵥ ((a • 1) *ᵥ x) = a • star x ⬝ᵥ x = a · ∑ |x i|²`.
    have h_eq : star x ⬝ᵥ (((a : ℝ) • (1 : Matrix n n ℂ)) *ᵥ x) = (a : ℂ) * (star x ⬝ᵥ x) := by
      simp [Matrix.smul_mulVec, Matrix.one_mulVec, Complex.real_smul]
    rw [h_eq]
    have hxx_nn : (0 : ℂ) ≤ (star x ⬝ᵥ x) := by
      have := (Matrix.PosSemidef.one (n := n) (R := ℂ)).dotProduct_mulVec_nonneg x
      simpa using this
    have ha_C : (0 : ℂ) ≤ (a : ℂ) := by
      rw [Complex.le_def]; refine ⟨by simpa using ha, by simp⟩
    exact mul_nonneg ha_C hxx_nn

/-- Loewner monotonicity of real-scalar smul on `Matrix n n ℂ` for the
identity matrix: `(a : ℝ) ≤ b → a • 1 ≤ b • 1`. -/
lemma _root_.Matrix.real_smul_one_le_smul_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {a b : ℝ} (hab : a ≤ b) :
    ((a : ℝ) • (1 : Matrix n n ℂ)) ≤ ((b : ℝ) • (1 : Matrix n n ℂ)) := by
  rw [Matrix.le_iff]
  have : (b : ℝ) • (1 : Matrix n n ℂ) - (a : ℝ) • (1 : Matrix n n ℂ)
      = (b - a) • (1 : Matrix n n ℂ) := by
    rw [← sub_smul]
  rw [this]
  exact Matrix.posSemidef_real_smul_one (by linarith)

set_option maxHeartbeats 800000 in
/-- **Sub-helper D2.** Loewner-form variance bound for the matrix Bernstein
hypothesis. The sum across `j : Fin m` of the expected matrix products
`∫ X_j · X_j ∂ν` (which collapse to `m · ∫ X·X ∂ν` since the family is iid)
is bounded above by `σ² · 1` in the Loewner order, where
`σ² := 4 n² M⁴ / m`. -/
lemma centeredNeuronNTKSummand_variance_loewner_le
    {n m : ℕ} [Nonempty (Fin n)] {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    ∑ _j : Fin m, ∫ wb, centeredNeuronNTKSummand σ xs ν m wb *
                    centeredNeuronNTKSummand σ xs ν m wb ∂ν
      ≤ (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  -- Set `K := ∫ X · X ∂ν`.
  set K : Matrix (Fin n) (Fin n) ℂ :=
    ∫ wb, centeredNeuronNTKSummand σ xs ν m wb *
            centeredNeuronNTKSummand σ xs ν m wb ∂ν with hK_def
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  -- `∑ _j : Fin m, K = m • K`.
  have h_sum_const : (∑ _j : Fin m, K) = (m : ℕ) • K := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- PSD of K and op-norm bound.
  have hK_psd : K.PosSemidef :=
    centeredNeuronNTKSummand_mul_self_integral_posSemidef hσ_meas hM hσ xs ν hm
  have hK_norm : ‖K‖ ≤ 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2 :=
    centeredNeuronNTKSummand_mul_self_integral_norm_le hM hσ xs ν hm
  -- Loewner bound on K: `K ≤ ‖K‖ • 1`.
  have hK_le : K ≤ (‖K‖ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) :=
    hK_psd.le_norm_smul_one_of_isHermitian
  rw [h_sum_const]
  -- `(m : ℕ) • K = (m : ℝ) • K`.
  have h_smul_eq : (m : ℕ) • K = ((m : ℝ) • K : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Nat.cast_smul_eq_nsmul]
  rw [h_smul_eq]
  have h_pos_m : (0 : ℝ) ≤ (m : ℝ) := hm_pos.le
  -- `(m : ℝ) • K ≤ (m : ℝ) • (‖K‖ • 1) = (m * ‖K‖) • 1`.
  have h_step1 : ((m : ℝ) • K : Matrix (Fin n) (Fin n) ℂ) ≤
      ((m : ℝ) * ‖K‖) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h_a : ((m : ℝ) • K : Matrix (Fin n) (Fin n) ℂ) ≤
        ((m : ℝ) • (((‖K‖ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ) :=
      smul_le_smul_of_nonneg_left hK_le h_pos_m
    have h_b : ((m : ℝ) • (((‖K‖ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)))
        : Matrix (Fin n) (Fin n) ℂ)
        = ((m : ℝ) * ‖K‖) • (1 : Matrix (Fin n) (Fin n) ℂ) := smul_smul _ _ _
    rw [← h_b]; exact h_a
  -- `(m * ‖K‖) • 1 ≤ (4 n² M⁴ / m) • 1` via real-scalar Loewner monotonicity.
  have h_scalar_le : (m : ℝ) * ‖K‖ ≤ 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) := by
    calc (m : ℝ) * ‖K‖
        ≤ (m : ℝ) * (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hK_norm h_pos_m
      _ = 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) := by
          have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
          field_simp
  exact h_step1.trans (Matrix.real_smul_one_le_smul_one h_scalar_le)

/-! ### Main theorem: sharp empirical-NTK matrix Bernstein concentration -/

set_option maxHeartbeats 800000 in
/-- **Sharp empirical-NTK matrix Bernstein concentration (ℂ-cast form).**

For a bounded measurable activation `|σ z| ≤ M` (with `0 < M`), an iid
sample of size `m` from a probability measure `ν`, and any radius
`t > 0`, the operator-norm deviation of the empirical NTK from the
population NTK satisfies the matrix Bernstein tail bound

    `P(t ≤ ‖(empiricalNTK σ xs ω - populationNTK σ xs ν).map ofReal‖)`
      `≤ 2 · matrix_bernstein_bound n t (4 n² M⁴ / m) (2 n M² / m)`.

The variance proxy `σ² := 4 n² M⁴ / m` and per-summand operator-norm
radius `R := 2 n M² / m` come from the per-summand bounds delivered by
Part C (`centeredNeuronNTKSummand_opNorm_le`,
`centeredNeuronNTKSummand_mul_self_opNorm_le`). The factor of `2` in
front of the carrier bound is the union-bound overhead from combining
the `λ_max(∑ X_i)` and `λ_max(-∑ X_i)` events in
`Matrix.bernstein_op_norm_full`.

The hypotheses `hSum`, `hLamMeasPos`, `hLamMeasNeg`, `htrIntPos`,
`htrIntNeg` are the regularity hypotheses propagated through from
`Matrix.bernstein_op_norm_full`: Hermitian-ness of the sample sum,
AE-measurability of the spectral suprema, and integrability of the
trace exponential. -/
theorem empiricalNTK_matrix_bernstein
    {n m : ℕ} [Nonempty (Fin n)]
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ) {M : ℝ} (hM : 0 < M)
    (hσ_bdd : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hm : 0 < m)
    {ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d) × ℝ)}
    [MeasureTheory.IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 < t)
    (hSum : ∀ ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ,
      (∑ i, centeredNeuronNTKSummand σ xs ν m (ω i)).IsHermitian)
    (hLamMeasPos : AEMeasurable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (hLamMeasNeg : AEMeasurable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).neg.eigenvalues)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (htrIntPos : MeasureTheory.Integrable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        (Matrix.trace (NormedSpace.exp
          (LTFP.matrix_bernstein_theta t (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
              (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) •
            (∑ i, centeredNeuronNTKSummand σ xs ν m (ω i))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (htrIntNeg : MeasureTheory.Integrable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        (Matrix.trace (NormedSpace.exp
          (LTFP.matrix_bernstein_theta t (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
              (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) •
            (∑ i, -(centeredNeuronNTKSummand σ xs ν m (ω i)))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν))) :
    (MeasureTheory.Measure.pi (fun _ : Fin m => ν)).real
      {ω | t ≤ ‖(empiricalNTK σ xs ω - populationNTK σ xs ν).map
          (fun r : ℝ => (r : ℂ))‖}
    ≤ 2 * LTFP.matrix_bernstein_bound n t
        (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
        (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) := by
  classical
  -- Set the family `X i ω := centeredNeuronNTKSummand σ xs ν m ω`
  -- (constant in `i`; the sample feeds through `ω i`).
  set X : Fin m → (EuclideanSpace ℝ (Fin d) × ℝ) → Matrix (Fin n) (Fin n) ℂ :=
    fun _ wb => centeredNeuronNTKSummand σ xs ν m wb with hX_def
  set μ : Fin m → MeasureTheory.Measure (EuclideanSpace ℝ (Fin d) × ℝ) :=
    fun _ => ν with hμ_def
  -- Per-summand hypotheses for `bernstein_op_norm_full`.
  have hM_nn : 0 ≤ M := hM.le
  have hX_herm : ∀ i ω, (X i ω).IsHermitian :=
    fun _ ω => centeredNeuronNTKSummand_isHermitian σ xs ν ω
  have hX_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (X i) (μ i) :=
    fun _ => centeredNeuronNTKSummand_aestronglyMeasurable hσ_meas xs ν
  set R : ℝ := 2 * (n : ℝ) * M ^ 2 / (m : ℝ) with hR_def
  set σ2 : ℝ := 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) with hσ2_def
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR_nn : 0 ≤ R := by rw [hR_def]; positivity
  have hX_bound : ∀ i ω, ‖X i ω‖ ≤ R :=
    fun _ ω => centeredNeuronNTKSummand_opNorm_le hM_nn hσ_bdd xs ν hm ω
  have hX_center : ∀ i, ∫ wb, X i wb ∂μ i = 0 :=
    fun _ => centeredNeuronNTKSummand_integral_eq_zero
      hσ_meas hM_nn hσ_bdd xs ν hm
  have hσ2_pos : 0 < σ2 := by
    rw [hσ2_def]
    have hM_pow : 0 < M ^ 4 := by positivity
    have hN_pow_pos : 0 ≤ (n : ℝ) ^ 2 := by positivity
    -- (n : ℝ) ≥ 1 since Fin n is nonempty.
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      have hcard : 0 < Fintype.card (Fin n) := Fintype.card_pos
      have hn_nat : 0 < n := by rwa [Fintype.card_fin] at hcard
      exact_mod_cast hn_nat
    positivity
  have hX_var : ∑ i, ∫ wb, X i wb * X i wb ∂μ i ≤ σ2 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hσ2_def]
    exact centeredNeuronNTKSummand_variance_loewner_le
      hσ_meas hM_nn hσ_bdd xs ν hm
  -- Apply `Matrix.bernstein_op_norm_full`.
  have h_bound := Matrix.bernstein_op_norm_full
    μ X hX_herm hX_meas R hR_nn hX_bound hX_center σ2 hσ2_pos hX_var t ht
    hSum hLamMeasPos hLamMeasNeg htrIntPos htrIntNeg
  -- Rewrite the event using `sum_centeredNeuronNTKSummand_eq_deviation`.
  have h_sum_eq : ∀ ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ,
      ∑ i, X i (ω i) = (empiricalNTK σ xs ω - populationNTK σ xs ν).map
          (fun r : ℝ => (r : ℂ)) := fun ω =>
    sum_centeredNeuronNTKSummand_eq_deviation σ xs ν hm ω
  have h_set_eq :
      {ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ | t ≤ ‖∑ i, X i (ω i)‖}
        = {ω | t ≤ ‖(empiricalNTK σ xs ω - populationNTK σ xs ν).map
              (fun r : ℝ => (r : ℂ))‖} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h_sum_eq ω]
  rw [← h_set_eq]
  -- Cast Fintype.card (Fin n) to n.
  rw [show (Fintype.card (Fin n) : ℕ) = n from Fintype.card_fin n] at h_bound
  exact h_bound

/-! ### Real-valued corollary

Stripping the entrywise `ℝ ↪ ℂ` cast from the deviation matrix, via the
bridge `Matrix.l2_opNorm_map_complex_ofReal : ‖A.map ofReal‖ = ‖A‖`. The
events `{ω | t ≤ ‖(D ω).map ofReal‖}` and `{ω | t ≤ ‖D ω‖}` are equal as
subsets of the sample space, so the probabilities coincide and the
ℂ-cast theorem transfers verbatim to the real-valued statement. -/

set_option maxHeartbeats 800000 in
/-- **Sharp empirical-NTK matrix Bernstein concentration (real form).**

The same statement as `empiricalNTK_matrix_bernstein`, but with the
deviation matrix viewed natively as a real matrix:

    `P(t ≤ ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖)`
      `≤ 2 · matrix_bernstein_bound n t (4 n² M⁴ / m) (2 n M² / m)`.

The L2 operator norm is invariant under the entrywise `ℝ ↪ ℂ` embedding
(`Matrix.l2_opNorm_map_complex_ofReal`), so the two formulations are
strictly equivalent on the level of sets. -/
theorem empiricalNTK_matrix_bernstein_real
    {n m : ℕ} [Nonempty (Fin n)]
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ) {M : ℝ} (hM : 0 < M)
    (hσ_bdd : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hm : 0 < m)
    {ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d) × ℝ)}
    [MeasureTheory.IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 < t)
    (hSum : ∀ ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ,
      (∑ i, centeredNeuronNTKSummand σ xs ν m (ω i)).IsHermitian)
    (hLamMeasPos : AEMeasurable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (hLamMeasNeg : AEMeasurable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).neg.eigenvalues)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (htrIntPos : MeasureTheory.Integrable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        (Matrix.trace (NormedSpace.exp
          (LTFP.matrix_bernstein_theta t (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
              (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) •
            (∑ i, centeredNeuronNTKSummand σ xs ν m (ω i))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (htrIntNeg : MeasureTheory.Integrable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        (Matrix.trace (NormedSpace.exp
          (LTFP.matrix_bernstein_theta t (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
              (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) •
            (∑ i, -(centeredNeuronNTKSummand σ xs ν m (ω i)))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν))) :
    (MeasureTheory.Measure.pi (fun _ : Fin m => ν)).real
      {ω | t ≤ ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖}
    ≤ 2 * LTFP.matrix_bernstein_bound n t
        (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
        (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) := by
  -- Apply the bridge: the events are equal because the L2 operator norm
  -- is invariant under the entrywise ℝ ↪ ℂ embedding.
  have h_set_eq :
      {ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ
          | t ≤ ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖}
        = {ω | t ≤ ‖(empiricalNTK σ xs ω - populationNTK σ xs ν).map
              (fun r : ℝ => (r : ℂ))‖} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
      Matrix.l2_opNorm_map_complex_ofReal]
  rw [h_set_eq]
  exact empiricalNTK_matrix_bernstein hσ_meas hM hσ_bdd xs hm ht
    hSum hLamMeasPos hLamMeasNeg htrIntPos htrIntNeg

end ProbabilityTheory
