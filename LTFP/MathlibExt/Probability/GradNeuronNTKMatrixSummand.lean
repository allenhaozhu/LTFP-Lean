/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import LTFP.MathlibExt.Probability.GradNeuronNTK
import LTFP.MathlibExt.Probability.NTKMatrixSummand
import LTFP.MathlibExt.Analysis.Matrix.OpNormByMax
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Matrix-valued centered gradient-block NTK summand (matrix Bernstein adapter)

**R4 NTK Part E1b.** Gradient-block analogue of the σ-block adapter in
`LTFP/MathlibExt/Probability/NTKMatrixSummand.lean`. Builds the
matrix-valued centered summand for the **gradient block** (`σ'`)
random-feature NTK, supplying the Hermitian-ness, integral-zero,
operator-norm and variance-norm side conditions consumed by
`Matrix.bernstein_full`
(`LTFP/MathlibExt/MatrixAnalysis/MatrixBernsteinFinal.lean`).

The scalar gradient-block contribution is

  `gradNeuronNTK σ' x x' wb = σ'(⟨w, x⟩ + b) · σ'(⟨w, x'⟩ + b) · ⟨x, x'⟩`

(see `LTFP/MathlibExt/Probability/GradNeuronNTK.lean`, Part E1a). The
entrywise pointwise envelope is `|gradNeuronNTK σ' x x' wb| ≤ M'² · G`
whenever `|σ' z| ≤ M'` and `|⟨x, x'⟩| ≤ G`, so the matrix
`(a, b) ↦ gradNeuronNTK σ' (xs a) (xs b) wb` has entrywise bound
`M'² · G` and the operator-norm machinery from
`LTFP/MathlibExt/Analysis/Matrix/OpNormByMax.lean`
(`Matrix.l2_opNorm_le_card_mul_of_entry_le_C`) gives
`‖·‖ ≤ n · (M'² · G)`.

## Main definitions

* `gradNeuronNTKMatrixC` — per-entry ℂ cast of the scalar gradient-block
  single-neuron NTK matrix.
* `centeredGradNeuronNTKSummand` — `(1/m) • (gradNeuronNTKMatrixC -
  (populationGradNTK).map Complex.ofReal)`, the centered scaled matrix
  summand whose sum recovers the empirical-minus-population
  gradient-block NTK deviation.

## Main results

* `sum_centeredGradNeuronNTKSummand_eq_deviation` — the sum identity.
* `gradNeuronNTKMatrixC_isHermitian` / `centeredGradNeuronNTKSummand_isHermitian`.
* `gradNeuronNTKMatrixC_opNorm_le` /
  `centeredGradNeuronNTKSummand_opNorm_le` — op-norm bounds.
* `centeredGradNeuronNTKSummand_apply_integral_eq_zero` — centering.
* `centeredGradNeuronNTKSummand_mul_self_opNorm_le` and
  `centeredGradNeuronNTKSummand_variance_norm_sum_le` — variance
  norm bounds.

All bounds carry the explicit `M'² · G` envelope (rather than `M²` from
the σ-block) because the gradient-block contribution multiplies by the
data-Gram factor `⟨x, x'⟩`, which Cauchy–Schwarz bounds by `G`.
-/

namespace ProbabilityTheory

open MeasureTheory BigOperators

variable {d : ℕ}

/-- **Matrix-valued single-neuron gradient-block NTK contribution** (ℂ-valued).

Cast of the scalar `gradNeuronNTK σ' (xs a) (xs b) wb` into a matrix
`Matrix (Fin n) (Fin n) ℂ`. This is the per-neuron summand that the
matrix Bernstein machinery consumes for the gradient block after
centering and scaling. -/
noncomputable def gradNeuronNTKMatrixC
    {n : ℕ}
    (σ' : ℝ → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun a b => (gradNeuronNTK σ' (xs a) (xs b) wb : ℂ)

/-- **Centered scaled matrix-valued gradient-block NTK summand.**

Given the population gradient-block NTK
`populationGradNTK σ' xs ν : Matrix (Fin n) (Fin n) ℝ`, the centered
single-neuron gradient-block contribution at width-scaling `1/m` is
`(1/m) • (gradNeuronNTKMatrixC σ' xs wb - (populationGradNTK σ' xs ν).map ofReal)`.

Summing over an iid sample `ω : Fin m → (ℝᵈ × ℝ)` recovers the
ℂ-cast of the empirical-minus-population gradient-block NTK deviation,
see `sum_centeredGradNeuronNTKSummand_eq_deviation`. -/
noncomputable def centeredGradNeuronNTKSummand
    {n : ℕ}
    (σ' : ℝ → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) (m : ℕ)
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / (m : ℝ)) •
    (gradNeuronNTKMatrixC σ' xs wb -
      (populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ)))

/-- **Sum identity.** Summing the centered scaled gradient-block matrix
summand over an iid sample of size `m` recovers the empirical-minus-
population gradient-block NTK deviation, cast entrywise to ℂ. -/
lemma sum_centeredGradNeuronNTKSummand_eq_deviation
    {n m : ℕ}
    (σ' : ℝ → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ))
    (hm : 0 < m) (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :
    ∑ j, centeredGradNeuronNTKSummand σ' xs ν m (ω j) =
      (empiricalGradNTK σ' xs ω - populationGradNTK σ' xs ν).map
        (fun r : ℝ => (r : ℂ)) := by
  ext a b
  simp only [Matrix.sum_apply, centeredGradNeuronNTKSummand,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply,
    gradNeuronNTKMatrixC]
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  simp only [Complex.real_smul]
  rw [← Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [empiricalGradNTK]
  push_cast
  have hm_ne_c : (m : ℂ) ≠ 0 := by exact_mod_cast hm_ne
  field_simp
  ring

/-! ### R4 NTK Part E1b — per-summand bounds for matrix Bernstein

Mirror of Part C in `NTKMatrixSummand.lean`, with the envelope
`M'² · G` replacing the σ-block envelope `M²` (because the gradient-
block contribution carries an extra data-Gram factor `⟨x, x'⟩` bounded
by `G`). The Loewner form of the variance bound (consumed by
`Matrix.bernstein_full`) follows from the operator-norm bound on each
summand plus the standard Hermitian fact `H² ≤ ‖H‖²_op • 1`, supplied
upstream in `LTFP/MathlibExt/MatrixAnalysis/BernsteinCFCLift.lean`. -/

/-! #### Hermitian-ness -/

/-- **Hermitian-ness of the matrix-valued single-neuron gradient-block NTK.**

The per-neuron gradient-block NTK matrix
`(a, b) ↦ (gradNeuronNTK σ' (xs a) (xs b) wb : ℂ)` is Hermitian because
`gradNeuronNTK σ' x x' wb = gradNeuronNTK σ' x' x wb` (data symmetry,
see `gradNeuronNTK_symm`) and the entries are real (hence fixed by
complex conjugation). -/
lemma gradNeuronNTKMatrixC_isHermitian
    {n : ℕ} (σ' : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    (gradNeuronNTKMatrixC σ' xs wb).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun i j => ?_)
  show star ((gradNeuronNTK σ' (xs j) (xs i) wb : ℝ) : ℂ)
       = ((gradNeuronNTK σ' (xs i) (xs j) wb : ℝ) : ℂ)
  rw [Complex.star_def, Complex.conj_ofReal]
  congr 1
  exact (gradNeuronNTK_symm σ' (xs j) (xs i) wb).trans rfl

/-- **Symmetry of the populationGradNTK matrix.** `populationGradNTK σ' xs ν`
is symmetric (a, b ↔ b, a) because the integrand `gradNeuronNTK` is
symmetric in the two data inputs. -/
lemma populationGradNTK_symm
    {n : ℕ} (σ' : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) (i j : Fin n) :
    populationGradNTK σ' xs ν i j = populationGradNTK σ' xs ν j i := by
  unfold populationGradNTK
  refine integral_congr_ae (Filter.Eventually.of_forall (fun wb => ?_))
  exact gradNeuronNTK_symm σ' (xs i) (xs j) wb

/-- **Hermitian-ness of the ℂ-cast of the populationGradNTK.** -/
lemma populationGradNTK_map_complex_isHermitian
    {n : ℕ} (σ' : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    ((populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ))).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun i j => ?_)
  show star (((populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ))) j i)
       = ((populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ))) i j
  simp only [Matrix.map_apply]
  rw [Complex.star_def, Complex.conj_ofReal]
  congr 1
  exact populationGradNTK_symm σ' xs ν j i

/-- **Hermitian-ness of the centered scaled gradient-block NTK summand.**

The centered scaled summand
`(1/m) • (gradNeuronNTKMatrixC σ' xs wb -
  (populationGradNTK σ' xs ν).map ofReal)` is Hermitian as the
smul-scaling of a difference of two Hermitians. -/
lemma centeredGradNeuronNTKSummand_isHermitian
    {n m : ℕ} (σ' : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ))
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    (centeredGradNeuronNTKSummand σ' xs ν m wb).IsHermitian := by
  unfold centeredGradNeuronNTKSummand
  have h_diff : (gradNeuronNTKMatrixC σ' xs wb -
      (populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ))).IsHermitian :=
    (gradNeuronNTKMatrixC_isHermitian σ' xs wb).sub
      (populationGradNTK_map_complex_isHermitian σ' xs ν)
  exact ((IsSelfAdjoint.all ((1 : ℝ) / (m : ℝ))).smul h_diff.isSelfAdjoint :
    IsSelfAdjoint _)

/-! #### Op-norm bound via entrywise sup -/

open scoped Matrix.Norms.L2Operator in
/-- **Operator-norm bound on the matrix-valued single-neuron gradient-block NTK.**

For a bounded derivative `|σ' z| ≤ M'` (with `0 ≤ M'`) and a data-Gram
envelope `|⟨xs a, xs b⟩| ≤ G` for all `a, b`, the per-neuron ℂ-cast
gradient-block NTK matrix has operator-norm at most `n · (M'² · G)`.

Proof: entrywise bound `|gradNeuronNTK| ≤ M'² · G` (from
`gradNeuronNTK_abs_le`) together with the Cauchy–Schwarz glue
`Matrix.l2_opNorm_le_card_mul_of_entry_le_C` with `s := M'² · G`. -/
lemma gradNeuronNTKMatrixC_opNorm_le
    {n : ℕ} (σ' : ℝ → ℝ) {M' G : ℝ} (hM' : 0 ≤ M') (hG_nn : 0 ≤ G)
    (hσ' : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    ‖gradNeuronNTKMatrixC σ' xs wb‖ ≤ (n : ℝ) * (M' ^ 2 * G) := by
  have hs_nn : 0 ≤ M' ^ 2 * G := mul_nonneg (by positivity) hG_nn
  have h_entry : ∀ i j : Fin n,
      ‖gradNeuronNTKMatrixC σ' xs wb i j‖ ≤ M' ^ 2 * G := by
    intro i j
    show ‖((gradNeuronNTK σ' (xs i) (xs j) wb : ℝ) : ℂ)‖ ≤ M' ^ 2 * G
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact gradNeuronNTK_abs_le hM' hσ' (hG i j) wb
  have := Matrix.l2_opNorm_le_card_mul_of_entry_le_C
    (gradNeuronNTKMatrixC σ' xs wb) hs_nn h_entry
  rwa [Fintype.card_fin] at this

open scoped Matrix.Norms.L2Operator in
/-- **Operator-norm bound on the centered scaled gradient-block NTK summand.**

`‖centeredGradNeuronNTKSummand σ' xs ν m wb‖ ≤ 2 · n · (M'² · G) / m`.
Triangle inequality plus the per-matrix bound
`gradNeuronNTKMatrixC_opNorm_le` and the analogous bound on the ℂ-cast
of `populationGradNTK` (obtained from the entrywise pointwise bound
under a probability measure). -/
lemma centeredGradNeuronNTKSummand_opNorm_le
    {n m : ℕ} {σ' : ℝ → ℝ} {M' G : ℝ}
    (hM' : 0 ≤ M') (hG_nn : 0 ≤ G) (hσ' : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    ‖centeredGradNeuronNTKSummand σ' xs ν m wb‖
      ≤ 2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ) := by
  unfold centeredGradNeuronNTKSummand
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (m : ℝ))]
  have h_K : ‖gradNeuronNTKMatrixC σ' xs wb‖ ≤ (n : ℝ) * (M' ^ 2 * G) :=
    gradNeuronNTKMatrixC_opNorm_le σ' hM' hG_nn hσ' xs hG wb
  -- Operator-norm bound on the ℂ-cast of populationGradNTK.
  have h_EK : ‖((populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ)))‖
      ≤ (n : ℝ) * (M' ^ 2 * G) := by
    have h_entry_R : ∀ a b : Fin n,
        |populationGradNTK σ' xs ν a b| ≤ M' ^ 2 * G := by
      intro a b
      unfold populationGradNTK
      have h_pt : ∀ wb', |gradNeuronNTK σ' (xs a) (xs b) wb'| ≤ M' ^ 2 * G :=
        fun wb' => gradNeuronNTK_abs_le hM' hσ' (hG a b) wb'
      have h_int_abs_le :
          |∫ wb', gradNeuronNTK σ' (xs a) (xs b) wb' ∂ν| ≤
            ∫ wb', |gradNeuronNTK σ' (xs a) (xs b) wb'| ∂ν :=
        abs_integral_le_integral_abs
      have h_int_abs_le' :
          ∫ wb', |gradNeuronNTK σ' (xs a) (xs b) wb'| ∂ν ≤ M' ^ 2 * G := by
        have h_bound :
            ∫ wb', |gradNeuronNTK σ' (xs a) (xs b) wb'| ∂ν ≤
              ∫ _wb' : EuclideanSpace ℝ (Fin d) × ℝ, M' ^ 2 * G ∂ν := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) ?_
            (Filter.Eventually.of_forall (fun wb' => h_pt wb'))
          exact integrable_const _
        calc ∫ wb', |gradNeuronNTK σ' (xs a) (xs b) wb'| ∂ν
            ≤ ∫ _wb' : EuclideanSpace ℝ (Fin d) × ℝ, M' ^ 2 * G ∂ν := h_bound
          _ = M' ^ 2 * G := by simp [integral_const, probReal_univ]
      exact h_int_abs_le.trans h_int_abs_le'
    have h_entry_C : ∀ a b : Fin n,
        ‖((populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ))) a b‖
          ≤ M' ^ 2 * G := by
      intro a b
      simp only [Matrix.map_apply]
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact h_entry_R a b
    have hs_nn : 0 ≤ M' ^ 2 * G := mul_nonneg (by positivity) hG_nn
    have := Matrix.l2_opNorm_le_card_mul_of_entry_le_C
      ((populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ))) hs_nn h_entry_C
    rwa [Fintype.card_fin] at this
  have h_sub : ‖gradNeuronNTKMatrixC σ' xs wb -
      (populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ))‖
      ≤ 2 * ((n : ℝ) * (M' ^ 2 * G)) := by
    calc ‖gradNeuronNTKMatrixC σ' xs wb -
            (populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ))‖
        ≤ ‖gradNeuronNTKMatrixC σ' xs wb‖ +
            ‖((populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ)))‖ :=
          norm_sub_le _ _
      _ ≤ (n : ℝ) * (M' ^ 2 * G) + (n : ℝ) * (M' ^ 2 * G) := by linarith
      _ = 2 * ((n : ℝ) * (M' ^ 2 * G)) := by ring
  calc 1 / (m : ℝ) * ‖gradNeuronNTKMatrixC σ' xs wb -
          (populationGradNTK σ' xs ν).map (fun r : ℝ => (r : ℂ))‖
      ≤ 1 / (m : ℝ) * (2 * ((n : ℝ) * (M' ^ 2 * G))) := by
        apply mul_le_mul_of_nonneg_left h_sub
        positivity
    _ = 2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ) := by
        field_simp

/-! #### Integral of the centered summand is zero (entrywise form) -/

/-- **Integrability of the scalar single-neuron gradient-block NTK.** A
bounded measurable scalar function on a probability measure space is
integrable. -/
lemma gradNeuronNTK_integrable
    {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    {M' G : ℝ} (hM' : 0 ≤ M') (hσ' : ∀ z, |σ' z| ≤ M')
    (x x' : EuclideanSpace ℝ (Fin d)) (hG : |inner ℝ x x'| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    Integrable (fun wb => gradNeuronNTK σ' x x' wb) ν := by
  refine Integrable.mono' (g := fun _ => M' ^ 2 * G) (integrable_const _) ?_ ?_
  · exact (gradNeuronNTK_measurable hσ'_meas x x').aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun wb => ?_)
    rw [Real.norm_eq_abs]
    exact gradNeuronNTK_abs_le hM' hσ' hG wb

/-- **Integrability of the ℂ-cast of the scalar gradient-block NTK.** -/
lemma gradNeuronNTK_complex_integrable
    {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    {M' G : ℝ} (hM' : 0 ≤ M') (hσ' : ∀ z, |σ' z| ≤ M')
    (x x' : EuclideanSpace ℝ (Fin d)) (hG : |inner ℝ x x'| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    Integrable (fun wb => ((gradNeuronNTK σ' x x' wb : ℝ) : ℂ)) ν := by
  refine Integrable.mono' (g := fun _ => M' ^ 2 * G) (integrable_const _) ?_ ?_
  · exact (Complex.continuous_ofReal.measurable.comp
      (gradNeuronNTK_measurable hσ'_meas x x')).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun wb => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact gradNeuronNTK_abs_le hM' hσ' hG wb

/-- **Centering identity (entrywise form).** For a bounded derivative
and a data-Gram envelope, the entrywise integral of the centered scaled
gradient-block summand is zero:
`∫ centeredGradNeuronNTKSummand σ' xs ν m wb a b ∂ν = 0`. -/
lemma centeredGradNeuronNTKSummand_apply_integral_eq_zero
    {n m : ℕ} {σ' : ℝ → ℝ} (hσ'_meas : Measurable σ')
    {M' G : ℝ} (hM' : 0 ≤ M') (hσ' : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) (a b : Fin n) :
    ∫ wb, centeredGradNeuronNTKSummand σ' xs ν m wb a b ∂ν = (0 : ℂ) := by
  have h_eq : ∀ wb, centeredGradNeuronNTKSummand σ' xs ν m wb a b
      = ((1 : ℂ) / (m : ℂ)) *
          (((gradNeuronNTK σ' (xs a) (xs b) wb : ℝ) : ℂ) -
            ((populationGradNTK σ' xs ν a b : ℝ) : ℂ)) := by
    intro wb
    unfold centeredGradNeuronNTKSummand
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply,
      gradNeuronNTKMatrixC, Complex.real_smul]
    push_cast; ring
  have h_fun_eq : (fun wb => centeredGradNeuronNTKSummand σ' xs ν m wb a b)
      = (fun wb => ((1 : ℂ) / (m : ℂ)) *
          (((gradNeuronNTK σ' (xs a) (xs b) wb : ℝ) : ℂ) -
            ((populationGradNTK σ' xs ν a b : ℝ) : ℂ))) := by
    funext wb; exact h_eq wb
  rw [h_fun_eq]
  have hN_int : Integrable
      (fun wb => ((gradNeuronNTK σ' (xs a) (xs b) wb : ℝ) : ℂ)) ν :=
    gradNeuronNTK_complex_integrable hσ'_meas hM' hσ' (xs a) (xs b) (hG a b) ν
  have hC_int : Integrable (fun _ : EuclideanSpace ℝ (Fin d) × ℝ =>
      ((populationGradNTK σ' xs ν a b : ℝ) : ℂ)) ν := integrable_const _
  rw [integral_const_mul]
  rw [integral_sub hN_int hC_int]
  rw [integral_const]
  have h_int_C : ∫ wb, ((gradNeuronNTK σ' (xs a) (xs b) wb : ℝ) : ℂ) ∂ν
      = ((∫ wb, gradNeuronNTK σ' (xs a) (xs b) wb ∂ν : ℝ) : ℂ) :=
    integral_ofReal (μ := ν) (𝕜 := ℂ)
  rw [h_int_C]
  unfold populationGradNTK
  simp

/-! #### Per-summand variance bound (operator-norm form) -/

open scoped Matrix.Norms.L2Operator in
/-- **Per-summand product op-norm bound.** For a bounded derivative
`|σ' z| ≤ M'` and a data-Gram envelope `|⟨xs a, xs b⟩| ≤ G`, the
operator norm of the product `X · X` for
`X := centeredGradNeuronNTKSummand σ' xs ν m wb` is bounded by
`(2 · n · (M'² · G) / m)²`. -/
lemma centeredGradNeuronNTKSummand_mul_self_opNorm_le
    {n m : ℕ} {σ' : ℝ → ℝ} {M' G : ℝ}
    (hM' : 0 ≤ M') (hG_nn : 0 ≤ G) (hσ' : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    ‖centeredGradNeuronNTKSummand σ' xs ν m wb *
        centeredGradNeuronNTKSummand σ' xs ν m wb‖
      ≤ (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 := by
  have h_norm_mul : ‖centeredGradNeuronNTKSummand σ' xs ν m wb *
      centeredGradNeuronNTKSummand σ' xs ν m wb‖ ≤
      ‖centeredGradNeuronNTKSummand σ' xs ν m wb‖ ^ 2 := by
    calc ‖centeredGradNeuronNTKSummand σ' xs ν m wb *
              centeredGradNeuronNTKSummand σ' xs ν m wb‖
        ≤ ‖centeredGradNeuronNTKSummand σ' xs ν m wb‖ *
            ‖centeredGradNeuronNTKSummand σ' xs ν m wb‖ := norm_mul_le _ _
      _ = ‖centeredGradNeuronNTKSummand σ' xs ν m wb‖ ^ 2 := by ring
  have h_norm_bound : ‖centeredGradNeuronNTKSummand σ' xs ν m wb‖
      ≤ 2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ) :=
    centeredGradNeuronNTKSummand_opNorm_le hM' hG_nn hσ' xs hG ν hm wb
  have h_norm_sq_bound :
      ‖centeredGradNeuronNTKSummand σ' xs ν m wb‖ ^ 2
      ≤ (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h_norm_bound 2
  linarith [h_norm_mul, h_norm_sq_bound]

open scoped Matrix.Norms.L2Operator in
/-- **Per-summand variance norm bound (sum form).** For a bounded
derivative `|σ' z| ≤ M'` and a data-Gram envelope `|⟨xs a, xs b⟩| ≤ G`,
the sum over `j = 1..m` of the operator norms of `X · X` (with
`X := centeredGradNeuronNTKSummand`) is bounded by
`4 · n² · (M'² · G)² / m`.

This is the **norm-form** of the variance bound. The Loewner-form
follows from the operator-norm bound on each summand plus the standard
Hermitian fact `H² ≤ ‖H‖²_op • 1`. -/
lemma centeredGradNeuronNTKSummand_variance_norm_sum_le
    {n m : ℕ} {σ' : ℝ → ℝ} {M' G : ℝ}
    (hM' : 0 ≤ M') (hG_nn : 0 ≤ G) (hσ' : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m)
    (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :
    ∑ j, ‖centeredGradNeuronNTKSummand σ' xs ν m (ω j) *
            centeredGradNeuronNTKSummand σ' xs ν m (ω j)‖
      ≤ 4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ) := by
  have h_each : ∀ j : Fin m,
      ‖centeredGradNeuronNTKSummand σ' xs ν m (ω j) *
        centeredGradNeuronNTKSummand σ' xs ν m (ω j)‖
        ≤ (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 :=
    fun j => centeredGradNeuronNTKSummand_mul_self_opNorm_le
      hM' hG_nn hσ' xs hG ν hm (ω j)
  calc ∑ j, ‖centeredGradNeuronNTKSummand σ' xs ν m (ω j) *
                centeredGradNeuronNTKSummand σ' xs ν m (ω j)‖
      ≤ ∑ _j : Fin m, (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2 :=
        Finset.sum_le_sum fun j _ => h_each j
    _ = (m : ℝ) * ((2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ) := by
        have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
        field_simp
        ring

end ProbabilityTheory
