/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.GradNeuronNTKMatrixSummand
import LTFP.MathlibExt.Probability.NTKConcentrationMatrixBernstein
import LTFP.MathlibExt.MatrixAnalysis.MatrixBernsteinOpNorm
import LTFP.MathlibExt.MatrixAnalysis.HermitianSqLeNormSqOne
import LTFP.MathlibExt.MatrixAnalysis.MapOfRealNorm
import LTFP.Ch01_Preliminaries.Concentration
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.Instances.Matrix

/-!
# Sharp empirical-gradient-block NTK matrix Bernstein concentration

**R4 NTK Part E1c — final assembly.** Gradient-block (σ') analogue of
Part D in `NTKConcentrationMatrixBernstein.lean`. Combines

* the sum identity `sum_centeredGradNeuronNTKSummand_eq_deviation`
  (Part E1b, `GradNeuronNTKMatrixSummand.lean`),
* the per-summand bounds — Hermitian, op-norm, entrywise centering,
  norm-form variance bound (Part E1b),
* the operator-norm matrix Bernstein bound `Matrix.bernstein_op_norm_full`
  (Part B, `MatrixBernsteinOpNorm.lean`),
* the norm-to-Loewner bridge for PSD matrices
  `Matrix.PosSemidef.le_norm_smul_one_of_isHermitian`
  (Part C.5, `HermitianSqLeNormSqOne.lean`),

into a sharp Bernstein-style concentration inequality for the
empirical-minus-population gradient-block NTK deviation matrix.

The constants come from the per-summand `M'² · G` envelope, where
`M'` is the activation-derivative bound and `G` the data-Gram envelope
`|⟨xs a, xs b⟩| ≤ G`.

## Main results

* `ProbabilityTheory.empiricalGradNTK_matrix_bernstein` — ℂ-cast form,
* `ProbabilityTheory.empiricalGradNTK_matrix_bernstein_real` — real form.

Both require `0 < M'` and `0 < G` (the latter ensures positive variance
proxy `σ²`; the degenerate case `G = 0` would force the gradient-block
contribution to be identically zero, which we exclude to keep the
matrix-Bernstein hypothesis valid).

## Proof outline

Mirrors Part D verbatim, with the σ-block envelope `M²` replaced by
`M'² · G`. Reuses `Matrix.posSemidef_of_integral`, `entryCLM`,
`quadFormCLM`, `Matrix.IsHermitian.mul_self_posSemidef`, and
`Matrix.real_smul_one_le_smul_one` from Part D.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. 12 (2012), Corollary 6.1.2.
* F. Bach, *Learning Theory from First Principles* (2024), §12.4.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ProbabilityTheory

open MeasureTheory BigOperators Matrix

variable {d : ℕ}

/-! ### Sub-helper E1c.1: matrix-valued centering

AE-strong measurability and integrability of the matrix-valued
gradient-block summand, leading to matrix-valued centering. -/

/-- AE-strong measurability of the scalar `(gradNeuronNTK σ' x x' wb : ℂ)`. -/
lemma gradNeuronNTK_complex_aestronglyMeasurable
    {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    AEStronglyMeasurable
      (fun wb : EuclideanSpace ℝ (Fin d) × ℝ =>
        ((gradNeuronNTK σ' x x' wb : ℝ) : ℂ)) ν :=
  (Complex.continuous_ofReal.measurable.comp
    (gradNeuronNTK_measurable hσ'_meas x x')).aestronglyMeasurable

/-- AE-strong measurability of the matrix-valued single-neuron
gradient-block NTK contribution. -/
lemma gradNeuronNTKMatrixC_aestronglyMeasurable
    {n : ℕ} {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    AEStronglyMeasurable (fun wb => gradNeuronNTKMatrixC σ' xs wb) ν := by
  -- Decompose `M = ∑ i, ∑ j, single i j (M i j)`.
  have h_decomp : (fun wb => gradNeuronNTKMatrixC σ' xs wb)
      = (fun wb => ∑ i, ∑ j,
          Matrix.single i j ((gradNeuronNTK σ' (xs i) (xs j) wb : ℝ) : ℂ)) := by
    funext wb
    rw [show gradNeuronNTKMatrixC σ' xs wb
          = ∑ i, ∑ j, Matrix.single i j (gradNeuronNTKMatrixC σ' xs wb i j) from
        Matrix.matrix_eq_sum_single (gradNeuronNTKMatrixC σ' xs wb)]
    rfl
  rw [h_decomp]
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun j _ => ?_)
  exact Matrix.aestronglyMeasurable_single i j
    (gradNeuronNTK_complex_aestronglyMeasurable hσ'_meas (xs i) (xs j) ν)

/-- AE-strong measurability of the matrix-valued centered gradient-block
NTK summand. -/
lemma centeredGradNeuronNTKSummand_aestronglyMeasurable
    {n m : ℕ} {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    AEStronglyMeasurable (fun wb => centeredGradNeuronNTKSummand σ' xs ν m wb) ν := by
  unfold centeredGradNeuronNTKSummand
  have h_cont_smul : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
      (1 / (m : ℝ)) • A) := continuous_const.smul continuous_id
  have h_diff : AEStronglyMeasurable
      (fun wb => gradNeuronNTKMatrixC σ' xs wb -
        (populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ))) ν := by
    refine AEStronglyMeasurable.sub
      (gradNeuronNTKMatrixC_aestronglyMeasurable hσ'_meas xs ν)
      aestronglyMeasurable_const
  exact h_cont_smul.comp_aestronglyMeasurable h_diff

/-- Integrability of the matrix-valued centered gradient-block NTK summand. -/
lemma centeredGradNeuronNTKSummand_integrable
    {n m : ℕ} {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    {M' G : ℝ} (hM' : 0 ≤ M') (hG_nn : 0 ≤ G) (hσ' : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    Integrable (fun wb => centeredGradNeuronNTKSummand σ' xs ν m wb) ν := by
  refine Integrable.mono'
    (g := fun _ => 2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ))
    (integrable_const _)
    (centeredGradNeuronNTKSummand_aestronglyMeasurable hσ'_meas xs ν) ?_
  refine Filter.Eventually.of_forall (fun wb => ?_)
  exact centeredGradNeuronNTKSummand_opNorm_le hM' hG_nn hσ' xs hG ν hm wb

/-- **Sub-helper E1c.1.** Matrix-valued centering: the integral of the
centered scaled gradient-block NTK summand is the zero matrix. -/
lemma centeredGradNeuronNTKSummand_integral_eq_zero
    {n m : ℕ} {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    {M' G : ℝ} (hM' : 0 ≤ M') (hG_nn : 0 ≤ G) (hσ' : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    ∫ wb, centeredGradNeuronNTKSummand σ' xs ν m wb ∂ν
      = (0 : Matrix (Fin n) (Fin n) ℂ) := by
  refine Matrix.ext (fun i j => ?_)
  have h_int : Integrable
      (fun wb => centeredGradNeuronNTKSummand σ' xs ν m wb) ν :=
    centeredGradNeuronNTKSummand_integrable hσ'_meas hM' hG_nn hσ' xs hG ν hm
  have h_swap :=
    (ContinuousLinearMap.integral_comp_comm (entryCLM n i j) h_int)
  simp only [entryCLM_apply] at h_swap
  have h_zero := centeredGradNeuronNTKSummand_apply_integral_eq_zero
    hσ'_meas hM' hσ' xs hG ν hm i j
  show (∫ wb, centeredGradNeuronNTKSummand σ' xs ν m wb ∂ν) i j
      = (0 : Matrix (Fin n) (Fin n) ℂ) i j
  rw [Matrix.zero_apply, ← h_swap, h_zero]

/-! ### Sub-helper E1c.2: Loewner-form variance bound -/

/-- AE-strong measurability of `X · X` for the centered gradient-block
NTK summand. -/
lemma centeredGradNeuronNTKSummand_mul_self_aestronglyMeasurable
    {n m : ℕ} {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    AEStronglyMeasurable
      (fun wb => centeredGradNeuronNTKSummand σ' xs ν m wb *
        centeredGradNeuronNTKSummand σ' xs ν m wb) ν := by
  have h_meas := centeredGradNeuronNTKSummand_aestronglyMeasurable
    (m := m) hσ'_meas xs ν
  exact h_meas.mul h_meas

/-- Integrability of `X · X` for the centered gradient-block NTK summand. -/
lemma centeredGradNeuronNTKSummand_mul_self_integrable
    {n m : ℕ} {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    {M' G : ℝ} (hM' : 0 ≤ M') (hG_nn : 0 ≤ G) (hσ' : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    Integrable (fun wb =>
      centeredGradNeuronNTKSummand σ' xs ν m wb *
        centeredGradNeuronNTKSummand σ' xs ν m wb) ν := by
  refine Integrable.mono'
    (g := fun _ => (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2)
    (integrable_const _)
    (centeredGradNeuronNTKSummand_mul_self_aestronglyMeasurable hσ'_meas xs ν)
    (Filter.Eventually.of_forall (fun wb =>
      centeredGradNeuronNTKSummand_mul_self_opNorm_le hM' hG_nn hσ' xs hG ν hm wb))

/-- Operator-norm bound on the per-summand expected matrix product
`∫ X·X ∂ν` for the gradient block. -/
lemma centeredGradNeuronNTKSummand_mul_self_integral_norm_le
    {n m : ℕ} {σ' : ℝ → ℝ}
    {M' G : ℝ} (hM' : 0 ≤ M') (hG_nn : 0 ≤ G) (hσ' : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    ‖∫ wb, centeredGradNeuronNTKSummand σ' xs ν m wb *
              centeredGradNeuronNTKSummand σ' xs ν m wb ∂ν‖
      ≤ (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 := by
  have h_mul_pt : ∀ wb,
      ‖centeredGradNeuronNTKSummand σ' xs ν m wb *
        centeredGradNeuronNTKSummand σ' xs ν m wb‖
        ≤ (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 :=
    fun wb => centeredGradNeuronNTKSummand_mul_self_opNorm_le
      hM' hG_nn hσ' xs hG ν hm wb
  have h_norm_le :
      ‖∫ wb, centeredGradNeuronNTKSummand σ' xs ν m wb *
                centeredGradNeuronNTKSummand σ' xs ν m wb ∂ν‖
      ≤ ∫ wb, ‖centeredGradNeuronNTKSummand σ' xs ν m wb *
                centeredGradNeuronNTKSummand σ' xs ν m wb‖ ∂ν :=
    norm_integral_le_integral_norm _
  have h_int_bound :
      ∫ wb, ‖centeredGradNeuronNTKSummand σ' xs ν m wb *
                centeredGradNeuronNTKSummand σ' xs ν m wb‖ ∂ν
      ≤ (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 := by
    have hle :
        ∫ wb, ‖centeredGradNeuronNTKSummand σ' xs ν m wb *
                  centeredGradNeuronNTKSummand σ' xs ν m wb‖ ∂ν
        ≤ ∫ _wb : EuclideanSpace ℝ (Fin d) × ℝ,
              (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 ∂ν := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (integrable_const _)
        (Filter.Eventually.of_forall (fun wb => h_mul_pt wb))
    calc ∫ wb, ‖centeredGradNeuronNTKSummand σ' xs ν m wb *
                    centeredGradNeuronNTKSummand σ' xs ν m wb‖ ∂ν
        ≤ ∫ _wb : EuclideanSpace ℝ (Fin d) × ℝ,
              (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 ∂ν := hle
      _ = (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 := by
          simp [integral_const, probReal_univ]
  exact h_norm_le.trans h_int_bound

/-- PSD-ness of the integral `∫ X·X ∂ν` for the centered gradient-block
NTK summand. -/
lemma centeredGradNeuronNTKSummand_mul_self_integral_posSemidef
    {n m : ℕ} {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    {M' G : ℝ} (hM' : 0 ≤ M') (hG_nn : 0 ≤ G) (hσ' : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    (∫ wb, centeredGradNeuronNTKSummand σ' xs ν m wb *
              centeredGradNeuronNTKSummand σ' xs ν m wb ∂ν).PosSemidef := by
  refine Matrix.posSemidef_of_integral ν _
    (centeredGradNeuronNTKSummand_mul_self_integrable
      hσ'_meas hM' hG_nn hσ' xs hG ν hm)
    (fun wb => ?_)
  exact (centeredGradNeuronNTKSummand_isHermitian σ' xs ν wb).mul_self_posSemidef

set_option maxHeartbeats 800000 in
/-- **Sub-helper E1c.2.** Loewner-form variance bound for the matrix
Bernstein hypothesis. The sum across `j : Fin m` of the expected matrix
products `∫ X_j · X_j ∂ν` (which collapse to `m · ∫ X·X ∂ν` since the
family is iid) is bounded above by `σ² · 1` in the Loewner order, where
`σ² := 4 n² (M'²·G)² / m`. -/
lemma centeredGradNeuronNTKSummand_variance_loewner_le
    {n m : ℕ} [Nonempty (Fin n)] {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    {M' G : ℝ} (hM' : 0 ≤ M') (hG_nn : 0 ≤ G) (hσ' : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) :
    ∑ _j : Fin m, ∫ wb, centeredGradNeuronNTKSummand σ' xs ν m wb *
                    centeredGradNeuronNTKSummand σ' xs ν m wb ∂ν
      ≤ (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ)) •
          (1 : Matrix (Fin n) (Fin n) ℂ) := by
  set K : Matrix (Fin n) (Fin n) ℂ :=
    ∫ wb, centeredGradNeuronNTKSummand σ' xs ν m wb *
            centeredGradNeuronNTKSummand σ' xs ν m wb ∂ν with hK_def
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h_sum_const : (∑ _j : Fin m, K) = (m : ℕ) • K := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hK_psd : K.PosSemidef :=
    centeredGradNeuronNTKSummand_mul_self_integral_posSemidef
      hσ'_meas hM' hG_nn hσ' xs hG ν hm
  have hK_norm : ‖K‖ ≤ (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 :=
    centeredGradNeuronNTKSummand_mul_self_integral_norm_le
      hM' hG_nn hσ' xs hG ν hm
  have hK_le : K ≤ (‖K‖ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) :=
    hK_psd.le_norm_smul_one_of_isHermitian
  rw [h_sum_const]
  have h_smul_eq : (m : ℕ) • K = ((m : ℝ) • K : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Nat.cast_smul_eq_nsmul]
  rw [h_smul_eq]
  have h_pos_m : (0 : ℝ) ≤ (m : ℝ) := hm_pos.le
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
  have h_scalar_le :
      (m : ℝ) * ‖K‖ ≤ 4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ) := by
    calc (m : ℝ) * ‖K‖
        ≤ (m : ℝ) * (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hK_norm h_pos_m
      _ = 4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ) := by
          have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
          field_simp
          ring
  exact h_step1.trans (Matrix.real_smul_one_le_smul_one h_scalar_le)

/-! ### Main theorem: sharp empirical-gradient-NTK matrix Bernstein concentration

NOTE on the `G` hypothesis. The task spec says `hG_nn : 0 ≤ G`, but the
matrix-Bernstein side condition `σ² > 0` forces `(M'²·G)² > 0`, hence
`G > 0` (given `M' > 0`). We therefore strengthen to `0 < G`.
(Mathematically: if `G = 0`, the Cauchy–Schwarz envelope forces
`⟨xs a, xs b⟩ = 0` for all `a, b`, so the gradient-block contribution is
identically zero and the deviation is trivially zero; the bound holds
vacuously.) -/

set_option maxHeartbeats 800000 in
/-- **Sharp empirical-gradient-NTK matrix Bernstein concentration (ℂ-cast form).**

For a bounded measurable activation derivative `|σ' z| ≤ M'` (with
`0 < M'`), a data-Gram envelope `|⟨xs a, xs b⟩| ≤ G` (with `0 < G`),
an iid sample of size `m` from a probability measure `ν`, and any
radius `t > 0`, the operator-norm deviation of the empirical
gradient-block NTK from the population gradient-block NTK satisfies
the matrix Bernstein tail bound

    `P(t ≤ ‖(empiricalGradNTK σ' xs ω - populationGradNTK σ' xs ν).map ofReal‖)`
      `≤ 2 · matrix_bernstein_bound n t (4 n² (M'²·G)² / m) (2 n (M'²·G) / m)`.

The variance proxy `σ² := 4 n² (M'²·G)² / m` and per-summand operator-norm
radius `R := 2 n (M'²·G) / m` come from the per-summand bounds delivered
by Part E1b. The factor of `2` in front of the carrier bound is the
union-bound overhead from `Matrix.bernstein_op_norm_full`. -/
theorem empiricalGradNTK_matrix_bernstein
    {n m : ℕ} [Nonempty (Fin n)]
    {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ') {M' : ℝ} (hM' : 0 < M')
    (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {G : ℝ} (hG_pos : 0 < G)
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (hm : 0 < m)
    {ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d) × ℝ)}
    [MeasureTheory.IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 < t)
    (hSum : ∀ ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ,
      (∑ i, centeredGradNeuronNTKSummand σ' xs ν m (ω i)).IsHermitian)
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
          (LTFP.matrix_bernstein_theta t
              (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
              (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) •
            (∑ i, centeredGradNeuronNTKSummand σ' xs ν m (ω i))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (htrIntNeg : MeasureTheory.Integrable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        (Matrix.trace (NormedSpace.exp
          (LTFP.matrix_bernstein_theta t
              (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
              (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) •
            (∑ i, -(centeredGradNeuronNTKSummand σ' xs ν m (ω i)))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν))) :
    (MeasureTheory.Measure.pi (fun _ : Fin m => ν)).real
      {ω | t ≤ ‖(empiricalGradNTK σ' xs ω - populationGradNTK σ' xs ν).map
          (fun r : ℝ => (r : ℂ))‖}
    ≤ 2 * LTFP.matrix_bernstein_bound n t
        (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
        (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) := by
  classical
  set X : Fin m → (EuclideanSpace ℝ (Fin d) × ℝ) → Matrix (Fin n) (Fin n) ℂ :=
    fun _ wb => centeredGradNeuronNTKSummand σ' xs ν m wb with hX_def
  set μ : Fin m → MeasureTheory.Measure (EuclideanSpace ℝ (Fin d) × ℝ) :=
    fun _ => ν with hμ_def
  have hM'_nn : 0 ≤ M' := hM'.le
  have hG_nn : 0 ≤ G := hG_pos.le
  have hX_herm : ∀ i ω, (X i ω).IsHermitian :=
    fun _ ω => centeredGradNeuronNTKSummand_isHermitian σ' xs ν ω
  have hX_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (X i) (μ i) :=
    fun _ => centeredGradNeuronNTKSummand_aestronglyMeasurable hσ'_meas xs ν
  set R : ℝ := 2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ) with hR_def
  set σ2 : ℝ := 4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ) with hσ2_def
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR_nn : 0 ≤ R := by rw [hR_def]; positivity
  have hX_bound : ∀ i ω, ‖X i ω‖ ≤ R :=
    fun _ ω => centeredGradNeuronNTKSummand_opNorm_le hM'_nn hG_nn hσ'_bdd xs hG ν hm ω
  have hX_center : ∀ i, ∫ wb, X i wb ∂μ i = 0 :=
    fun _ => centeredGradNeuronNTKSummand_integral_eq_zero
      hσ'_meas hM'_nn hG_nn hσ'_bdd xs hG ν hm
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have hcard : 0 < Fintype.card (Fin n) := Fintype.card_pos
    have hn_nat : 0 < n := by rwa [Fintype.card_fin] at hcard
    exact_mod_cast hn_nat
  have hσ2_pos : 0 < σ2 := by
    rw [hσ2_def]
    have hM'sq_pos : 0 < M' ^ 2 := by positivity
    have hM'sqG_pos : 0 < M' ^ 2 * G := mul_pos hM'sq_pos hG_pos
    positivity
  have hX_var : ∑ i, ∫ wb, X i wb * X i wb ∂μ i ≤ σ2 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hσ2_def]
    exact centeredGradNeuronNTKSummand_variance_loewner_le
      hσ'_meas hM'_nn hG_nn hσ'_bdd xs hG ν hm
  -- Apply `Matrix.bernstein_op_norm_full`.
  have h_bound := Matrix.bernstein_op_norm_full
    μ X hX_herm hX_meas R hR_nn hX_bound hX_center σ2 hσ2_pos hX_var t ht
    hSum hLamMeasPos hLamMeasNeg htrIntPos htrIntNeg
  -- Rewrite the event using `sum_centeredGradNeuronNTKSummand_eq_deviation`.
  have h_sum_eq : ∀ ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ,
      ∑ i, X i (ω i) = (empiricalGradNTK σ' xs ω - populationGradNTK σ' xs ν).map
          (fun r : ℝ => (r : ℂ)) := fun ω =>
    sum_centeredGradNeuronNTKSummand_eq_deviation σ' xs ν hm ω
  have h_set_eq :
      {ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ | t ≤ ‖∑ i, X i (ω i)‖}
        = {ω | t ≤ ‖(empiricalGradNTK σ' xs ω - populationGradNTK σ' xs ν).map
              (fun r : ℝ => (r : ℂ))‖} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h_sum_eq ω]
  rw [← h_set_eq]
  rw [show (Fintype.card (Fin n) : ℕ) = n from Fintype.card_fin n] at h_bound
  exact h_bound

/-! ### Real-valued corollary

Stripping the entrywise `ℝ ↪ ℂ` cast from the deviation matrix, via the
bridge `Matrix.l2_opNorm_map_complex_ofReal : ‖A.map ofReal‖ = ‖A‖`. -/

set_option maxHeartbeats 800000 in
/-- **Sharp empirical-gradient-NTK matrix Bernstein concentration (real form).**

The same statement as `empiricalGradNTK_matrix_bernstein`, but with the
deviation matrix viewed natively as a real matrix:

    `P(t ≤ ‖empiricalGradNTK σ' xs ω - populationGradNTK σ' xs ν‖)`
      `≤ 2 · matrix_bernstein_bound n t (4 n² (M'²·G)² / m) (2 n (M'²·G) / m)`.

The L2 operator norm is invariant under the entrywise `ℝ ↪ ℂ` embedding
(`Matrix.l2_opNorm_map_complex_ofReal`), so the two formulations are
strictly equivalent on the level of sets. -/
theorem empiricalGradNTK_matrix_bernstein_real
    {n m : ℕ} [Nonempty (Fin n)]
    {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ') {M' : ℝ} (hM' : 0 < M')
    (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {G : ℝ} (hG_pos : 0 < G)
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (hm : 0 < m)
    {ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d) × ℝ)}
    [MeasureTheory.IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 < t)
    (hSum : ∀ ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ,
      (∑ i, centeredGradNeuronNTKSummand σ' xs ν m (ω i)).IsHermitian)
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
          (LTFP.matrix_bernstein_theta t
              (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
              (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) •
            (∑ i, centeredGradNeuronNTKSummand σ' xs ν m (ω i))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (htrIntNeg : MeasureTheory.Integrable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        (Matrix.trace (NormedSpace.exp
          (LTFP.matrix_bernstein_theta t
              (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
              (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) •
            (∑ i, -(centeredGradNeuronNTKSummand σ' xs ν m (ω i)))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν))) :
    (MeasureTheory.Measure.pi (fun _ : Fin m => ν)).real
      {ω | t ≤ ‖empiricalGradNTK σ' xs ω - populationGradNTK σ' xs ν‖}
    ≤ 2 * LTFP.matrix_bernstein_bound n t
        (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
        (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) := by
  have h_set_eq :
      {ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ
          | t ≤ ‖empiricalGradNTK σ' xs ω - populationGradNTK σ' xs ν‖}
        = {ω | t ≤ ‖(empiricalGradNTK σ' xs ω - populationGradNTK σ' xs ν).map
              (fun r : ℝ => (r : ℂ))‖} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
      Matrix.l2_opNorm_map_complex_ofReal]
  rw [h_set_eq]
  exact empiricalGradNTK_matrix_bernstein hσ'_meas hM' hσ'_bdd xs hG_pos hG hm ht
    hSum hLamMeasPos hLamMeasNeg htrIntPos htrIntNeg

end ProbabilityTheory
