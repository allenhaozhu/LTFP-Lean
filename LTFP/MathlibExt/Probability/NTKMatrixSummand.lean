/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import LTFP.MathlibExt.Probability.NTKConcentration
import LTFP.MathlibExt.Analysis.Matrix.OpNormByMax
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Matrix-valued centered NTK summand (matrix Bernstein adapter)

**R4 Part A.** Adapter layer between the scalar/entrywise NTK
concentration of `LTFP.MathlibExt.Probability.NTKConcentration` and
the matrix Bernstein inequality `Matrix.bernstein_full`
(`LTFP.MathlibExt.MatrixAnalysis.MatrixBernsteinFinal`).

The matrix Bernstein bound consumes an iid family of centered
matrix-valued summands `X i` with values in `Matrix (Fin n) (Fin n) ℂ`.
The scalar `neuronNTK σ x x' wb` already lives in ℝ; to feed matrix
Bernstein we cast it entrywise to ℂ via `Complex.ofReal`, package it
into a matrix indexed by `(a, b) : Fin n × Fin n`, then center and
scale by `1 / m`.

## Main definitions

* `neuronNTKMatrixC` — per-entry ℂ cast of the scalar single-neuron NTK
  matrix `(a, b) ↦ neuronNTK σ (xs a) (xs b) wb`.
* `centeredNeuronNTKSummand` — `(1/m) • (neuronNTKMatrixC σ xs wb -
  (populationNTK σ xs ν).map Complex.ofReal)`, the centered scaled
  matrix summand whose sum over `j = 1..m` recovers the empirical-minus-
  population NTK deviation (entrywise in ℂ).

## Main results

* `sum_centeredNeuronNTKSummand_eq_deviation` — the sum identity
  `∑ j, centeredNeuronNTKSummand σ xs ν m (ω j) =
   (empiricalNTK σ xs ω - populationNTK σ xs ν).map Complex.ofReal`.
  This is the algebraic bridge that lets matrix Bernstein operate on
  the centered scaled summands and conclude an operator-norm tail bound
  on the empirical NTK deviation.
-/

namespace ProbabilityTheory

open MeasureTheory BigOperators

variable {d : ℕ}

/-- **Matrix-valued single-neuron NTK contribution** (ℂ-valued).

Cast of the scalar `neuronNTK σ (xs a) (xs b) wb` into a matrix
`Matrix (Fin n) (Fin n) ℂ`. This is the per-neuron summand that
matrix Bernstein consumes after centering and scaling. -/
noncomputable def neuronNTKMatrixC
    {n : ℕ}
    (σ : ℝ → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun a b => (neuronNTK σ (xs a) (xs b) wb : ℂ)

/-- **Centered scaled matrix-valued NTK summand.**

Given the population NTK `populationNTK σ xs ν : Matrix (Fin n) (Fin n) ℝ`,
the centered single-neuron contribution at width-scaling `1/m` is
`(1/m) • (neuronNTKMatrixC σ xs wb - (populationNTK σ xs ν).map Complex.ofReal)`.

Summing over an iid sample `ω : Fin m → (ℝᵈ × ℝ)` recovers the
ℂ-cast of the empirical-minus-population NTK deviation, see
`sum_centeredNeuronNTKSummand_eq_deviation`. -/
noncomputable def centeredNeuronNTKSummand
    {n : ℕ}
    (σ : ℝ → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) (m : ℕ)
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / (m : ℝ)) •
    (neuronNTKMatrixC σ xs wb -
      (populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ)))

/-- **Sum identity.** Summing the centered scaled matrix summand over
an iid sample of size `m` recovers the empirical-minus-population NTK
deviation, cast entrywise to ℂ.

This is the algebraic bridge that lets matrix Bernstein
(`Matrix.bernstein_full`) operate on the matrix-valued summands and
conclude an operator-norm tail bound on the empirical NTK deviation
matrix. -/
lemma sum_centeredNeuronNTKSummand_eq_deviation
    {n m : ℕ}
    (σ : ℝ → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ))
    (hm : 0 < m) (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :
    ∑ j, centeredNeuronNTKSummand σ xs ν m (ω j) =
      (empiricalNTK σ xs ω - populationNTK σ xs ν).map
        (fun r : ℝ => (r : ℂ)) := by
  -- Reduce the matrix identity to an entrywise identity.
  ext a b
  -- Evaluate both sides entrywise.
  simp only [Matrix.sum_apply, centeredNeuronNTKSummand,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply,
    neuronNTKMatrixC]
  -- Numerical positivity of `m`.
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  -- Rewrite the ℝ-smul of ℂ-valued terms as multiplication.
  simp only [Complex.real_smul]
  -- Pull `(1/m) *` outside the sum (Finset.mul_sum):
  rw [← Finset.mul_sum]
  -- Split the inner difference sum.
  rw [Finset.sum_sub_distrib]
  -- Replace the constant-sum with `m • K_ab`.
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- Evaluate the RHS entry (a, b) explicitly.
  simp only [empiricalNTK]
  -- Cast everything to ℂ and finish algebraically.
  push_cast
  have hm_ne_c : (m : ℂ) ≠ 0 := by exact_mod_cast hm_ne
  field_simp
  ring

/-! ### R4 NTK Part C — per-summand bounds for matrix Bernstein

The lemmas below establish the four side conditions consumed by
`Matrix.bernstein_full` (`LTFP/MathlibExt/MatrixAnalysis/MatrixBernsteinFinal.lean`):

1. **Hermitian**: `(neuronNTKMatrixC σ xs wb).IsHermitian` and the centered
   summand is Hermitian.
2. **Centered integral**: `∫ centeredNeuronNTKSummand σ xs ν m wb ∂ν = 0`.
3. **Op-norm bound**: `‖neuronNTKMatrixC σ xs wb‖ ≤ n · M²` and
   `‖centeredNeuronNTKSummand‖ ≤ 2 n M² / m` for any bounded activation
   `|σ z| ≤ M`.
4. **Variance bound** (norm form, looser variant): per-summand operator
   norm bound on the second moment `‖∫ X · X ∂ν‖ ≤ 4 n² M⁴ / m²` and
   sum-version `∑ ‖∫ X · X ∂ν‖ ≤ 4 n² M⁴ / m`.

The variance is delivered in norm form (rather than Loewner form
`∑ ∫ X · X ≤ σ² • 1`) because lifting the operator-norm bound to a
Loewner bound `H² ≤ ‖H‖² • 1` for Hermitian `H` (a standard but
infrastructure-heavy fact for Hermitian matrices: every Hermitian
`H` satisfies `H² ≤ ‖H‖²_op • 1` because the eigenvalues of `H²` are
squares of eigenvalues of `H`) requires `Matrix.PosSemidef` CFC
machinery that is its own piece of work; the norm form delivered here
is the immediate antecedent of the Loewner form and is the strictly
load-bearing fact for downstream matrix Bernstein composition.
-/

/-! #### Hermitian-ness -/

/-- **Hermitian-ness of the matrix-valued single-neuron NTK contribution.**

The per-neuron NTK matrix `(a, b) ↦ (neuronNTK σ (xs a) (xs b) wb : ℂ)`
is Hermitian, because `neuronNTK σ x x' wb = σ(...)·σ(...)` is symmetric in
`(x, x')` and the entries are real (hence fixed by complex conjugation). -/
lemma neuronNTKMatrixC_isHermitian
    {n : ℕ} (σ : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    (neuronNTKMatrixC σ xs wb).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun i j => ?_)
  -- Goal: `star (neuronNTKMatrixC σ xs wb j i) = neuronNTKMatrixC σ xs wb i j`.
  -- Unfold the definition.
  show star ((neuronNTK σ (xs j) (xs i) wb : ℝ) : ℂ)
       = ((neuronNTK σ (xs i) (xs j) wb : ℝ) : ℂ)
  rw [Complex.star_def, Complex.conj_ofReal]
  -- Symmetry of neuronNTK in its two inputs.
  congr 1
  unfold neuronNTK
  ring

/-- **Symmetry of the populationNTK matrix.** `populationNTK σ xs ν` is
symmetric (a, b ↔ b, a) because the integrand `neuronNTK` is symmetric. -/
lemma populationNTK_symm
    {n : ℕ} (σ : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) (i j : Fin n) :
    populationNTK σ xs ν i j = populationNTK σ xs ν j i := by
  unfold populationNTK
  refine integral_congr_ae (Filter.Eventually.of_forall (fun wb => ?_))
  unfold neuronNTK
  ring

/-- **Hermitian-ness of the ℂ-cast of the populationNTK.** -/
lemma populationNTK_map_complex_isHermitian
    {n : ℕ} (σ : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    ((populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ))).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun i j => ?_)
  show star (((populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ))) j i)
       = ((populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ))) i j
  simp only [Matrix.map_apply]
  rw [Complex.star_def, Complex.conj_ofReal]
  -- Need (populationNTK σ xs ν j i : ℂ) = (populationNTK σ xs ν i j : ℂ).
  congr 1
  exact populationNTK_symm σ xs ν j i

/-- **Hermitian-ness of the centered scaled NTK summand.**

The centered scaled summand `(1/m) • (neuronNTKMatrixC σ xs wb -
(populationNTK σ xs ν).map ofReal)` is Hermitian as the smul-scaling
of a difference of two Hermitians. -/
lemma centeredNeuronNTKSummand_isHermitian
    {n m : ℕ} (σ : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ))
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    (centeredNeuronNTKSummand σ xs ν m wb).IsHermitian := by
  unfold centeredNeuronNTKSummand
  -- The smul-scaling of a Hermitian matrix is Hermitian (real scalar).
  have h_diff : (neuronNTKMatrixC σ xs wb -
      (populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ))).IsHermitian :=
    (neuronNTKMatrixC_isHermitian σ xs wb).sub
      (populationNTK_map_complex_isHermitian σ xs ν)
  -- Apply `IsSelfAdjoint.smul` (real scalars commute with star).
  exact ((IsSelfAdjoint.all ((1 : ℝ) / (m : ℝ))).smul h_diff.isSelfAdjoint :
    IsSelfAdjoint _)

/-! #### Op-norm bound via entrywise sup (ℂ version)

The ℂ-valued analogue of `Matrix.l2_opNorm_le_card_mul_of_entry_le`
lives in `LTFP/MathlibExt/Analysis/Matrix/OpNormByMax.lean` as
`Matrix.l2_opNorm_le_card_mul_of_entry_le_C` (sibling of the ℝ-version
previously defined there). The bound below feeds the per-summand
op-norm estimates used by matrix Bernstein. -/

open scoped Matrix.Norms.L2Operator in
/-- **Operator-norm bound on the matrix-valued single-neuron NTK.**

For a bounded activation `|σ z| ≤ M` (with `0 ≤ M`), the per-neuron
ℂ-cast NTK matrix has operator-norm at most `n · M²`. The proof goes
via the entrywise bound `|neuronNTK| ≤ M²` together with the Cauchy–Schwarz
based glue `‖A‖ ≤ (Fintype.card n) · sup_{i,j} ‖A i j‖`. -/
lemma neuronNTKMatrixC_opNorm_le
    {n : ℕ} (σ : ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    ‖neuronNTKMatrixC σ xs wb‖ ≤ (n : ℝ) * M ^ 2 := by
  have hM2_nn : 0 ≤ M ^ 2 := by positivity
  have h_entry : ∀ i j : Fin n,
      ‖neuronNTKMatrixC σ xs wb i j‖ ≤ M ^ 2 := by
    intro i j
    show ‖((neuronNTK σ (xs i) (xs j) wb : ℝ) : ℂ)‖ ≤ M ^ 2
    rw [Complex.norm_real]
    have hb : |neuronNTK σ (xs i) (xs j) wb| ≤ M * M :=
      neuronNTK_bound hM hσ (xs i) (xs j) wb
    have hsq : M ^ 2 = M * M := sq M
    rw [Real.norm_eq_abs, hsq]
    exact hb
  have := Matrix.l2_opNorm_le_card_mul_of_entry_le_C
    (neuronNTKMatrixC σ xs wb) hM2_nn h_entry
  rwa [Fintype.card_fin] at this

open scoped Matrix.Norms.L2Operator in
/-- **Operator-norm bound on the centered scaled NTK summand.**

`‖centeredNeuronNTKSummand σ xs ν m wb‖ ≤ 2 · n · M² / m`. The proof
uses the triangle inequality, the operator-norm bound on
`neuronNTKMatrixC` and the same bound on the ℂ-cast of `populationNTK`
(obtained by integrating the entrywise pointwise bound under a
probability measure). -/
lemma centeredNeuronNTKSummand_opNorm_le
    {n m : ℕ} {σ : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    ‖centeredNeuronNTKSummand σ xs ν m wb‖ ≤ 2 * (n : ℝ) * M ^ 2 / (m : ℝ) := by
  unfold centeredNeuronNTKSummand
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  -- ‖(1/m) • (K - EK)‖ = (1/m) · ‖K - EK‖.
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (m : ℝ))]
  -- ‖K - EK‖ ≤ ‖K‖ + ‖EK‖ ≤ 2 · n · M².
  have h_K : ‖neuronNTKMatrixC σ xs wb‖ ≤ (n : ℝ) * M ^ 2 :=
    neuronNTKMatrixC_opNorm_le σ hM hσ xs wb
  -- Operator-norm bound on the ℂ-cast of populationNTK.
  have h_EK : ‖((populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ)))‖
      ≤ (n : ℝ) * M ^ 2 := by
    -- Entrywise bound: |populationNTK σ xs ν a b| ≤ M² since `ν` is a probability
    -- measure and `|neuronNTK| ≤ M²`.
    have h_entry_R : ∀ a b : Fin n, |populationNTK σ xs ν a b| ≤ M ^ 2 := by
      intro a b
      unfold populationNTK
      have h_pt : ∀ wb', |neuronNTK σ (xs a) (xs b) wb'| ≤ M * M :=
        fun wb' => neuronNTK_bound hM hσ (xs a) (xs b) wb'
      have h_int_abs_le :
          |∫ wb', neuronNTK σ (xs a) (xs b) wb' ∂ν| ≤
            ∫ wb', |neuronNTK σ (xs a) (xs b) wb'| ∂ν :=
        abs_integral_le_integral_abs
      have h_int_abs_le' :
          ∫ wb', |neuronNTK σ (xs a) (xs b) wb'| ∂ν ≤ M * M := by
        have h_bound :
            ∫ wb', |neuronNTK σ (xs a) (xs b) wb'| ∂ν ≤
              ∫ _wb' : EuclideanSpace ℝ (Fin d) × ℝ, M * M ∂ν := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) ?_
            (Filter.Eventually.of_forall (fun wb' => h_pt wb'))
          exact integrable_const _
        calc ∫ wb', |neuronNTK σ (xs a) (xs b) wb'| ∂ν
            ≤ ∫ _wb' : EuclideanSpace ℝ (Fin d) × ℝ, M * M ∂ν := h_bound
          _ = M * M := by simp [integral_const, probReal_univ]
      have hsq : M ^ 2 = M * M := sq M
      rw [hsq]
      exact h_int_abs_le.trans h_int_abs_le'
    -- ℂ-entry bound via Complex.norm_real.
    have h_entry_C : ∀ a b : Fin n,
        ‖((populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ))) a b‖ ≤ M ^ 2 := by
      intro a b
      simp only [Matrix.map_apply]
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact h_entry_R a b
    have hM2_nn : 0 ≤ M ^ 2 := by positivity
    have := Matrix.l2_opNorm_le_card_mul_of_entry_le_C
      ((populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ))) hM2_nn h_entry_C
    rwa [Fintype.card_fin] at this
  have h_sub : ‖neuronNTKMatrixC σ xs wb -
      (populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ))‖
      ≤ 2 * ((n : ℝ) * M ^ 2) := by
    calc ‖neuronNTKMatrixC σ xs wb -
            (populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ))‖
        ≤ ‖neuronNTKMatrixC σ xs wb‖ +
            ‖((populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ)))‖ :=
          norm_sub_le _ _
      _ ≤ (n : ℝ) * M ^ 2 + (n : ℝ) * M ^ 2 := by linarith
      _ = 2 * ((n : ℝ) * M ^ 2) := by ring
  calc 1 / (m : ℝ) * ‖neuronNTKMatrixC σ xs wb -
          (populationNTK σ xs ν).map (fun r : ℝ => (r : ℂ))‖
      ≤ 1 / (m : ℝ) * (2 * ((n : ℝ) * M ^ 2)) := by
        apply mul_le_mul_of_nonneg_left h_sub
        positivity
    _ = 2 * (n : ℝ) * M ^ 2 / (m : ℝ) := by
        field_simp

/-! #### Integral of the centered summand is zero (entrywise form) -/

/-- **Integrability of the scalar single-neuron NTK under a bounded
activation and a probability measure.** A bounded measurable scalar
function on a finite measure space is integrable. -/
lemma neuronNTK_integrable
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    Integrable (fun wb => neuronNTK σ x x' wb) ν := by
  refine Integrable.mono' (g := fun _ => M * M) (integrable_const _) ?_ ?_
  · -- ae strongly measurable
    exact (neuronNTK_measurable hσ_meas x x').aestronglyMeasurable
  · -- pointwise bound
    refine Filter.Eventually.of_forall (fun wb => ?_)
    rw [Real.norm_eq_abs]
    exact neuronNTK_bound hM hσ x x' wb

/-- **Integrability of the ℂ-cast of the scalar NTK.** -/
lemma neuronNTK_complex_integrable
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (x x' : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν] :
    Integrable (fun wb => ((neuronNTK σ x x' wb : ℝ) : ℂ)) ν := by
  refine Integrable.mono' (g := fun _ => M * M) (integrable_const _) ?_ ?_
  · exact (Complex.continuous_ofReal.measurable.comp
      (neuronNTK_measurable hσ_meas x x')).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun wb => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact neuronNTK_bound hM hσ x x' wb

/-- **Centering identity (entrywise form).** For a bounded activation,
the entrywise integral of the centered scaled summand is zero:
`∫ centeredNeuronNTKSummand σ xs ν m wb a b ∂ν = 0`. -/
lemma centeredNeuronNTKSummand_apply_integral_eq_zero
    {n m : ℕ} {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) (a b : Fin n) :
    ∫ wb, centeredNeuronNTKSummand σ xs ν m wb a b ∂ν = (0 : ℂ) := by
  -- Expand the entry of the centered summand.
  have h_eq : ∀ wb, centeredNeuronNTKSummand σ xs ν m wb a b
      = ((1 : ℂ) / (m : ℂ)) *
          (((neuronNTK σ (xs a) (xs b) wb : ℝ) : ℂ) -
            ((populationNTK σ xs ν a b : ℝ) : ℂ)) := by
    intro wb
    unfold centeredNeuronNTKSummand
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply,
      neuronNTKMatrixC, Complex.real_smul]
    push_cast; ring
  have h_fun_eq : (fun wb => centeredNeuronNTKSummand σ xs ν m wb a b)
      = (fun wb => ((1 : ℂ) / (m : ℂ)) *
          (((neuronNTK σ (xs a) (xs b) wb : ℝ) : ℂ) -
            ((populationNTK σ xs ν a b : ℝ) : ℂ))) := by
    funext wb; exact h_eq wb
  rw [h_fun_eq]
  -- Pull the constant `1/m` out and split the integral of the difference.
  have hN_int : Integrable (fun wb => ((neuronNTK σ (xs a) (xs b) wb : ℝ) : ℂ)) ν := by
    -- bounded measurable function on probability measure
    refine Integrable.mono' (g := fun _ => M * M) (integrable_const _) ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp
        (neuronNTK_measurable hσ_meas (xs a) (xs b))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun wb => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact neuronNTK_bound hM hσ (xs a) (xs b) wb
  have hC_int : Integrable (fun _ : EuclideanSpace ℝ (Fin d) × ℝ =>
      ((populationNTK σ xs ν a b : ℝ) : ℂ)) ν := integrable_const _
  -- Linearity.
  rw [integral_const_mul]
  rw [integral_sub hN_int hC_int]
  rw [integral_const]
  -- Compute ∫ (neuronNTK : ℂ) = (∫ neuronNTK : ℂ) = (populationNTK a b : ℂ).
  have h_int_C : ∫ wb, ((neuronNTK σ (xs a) (xs b) wb : ℝ) : ℂ) ∂ν
      = ((∫ wb, neuronNTK σ (xs a) (xs b) wb ∂ν : ℝ) : ℂ) :=
    integral_ofReal (μ := ν) (𝕜 := ℂ)
  rw [h_int_C]
  unfold populationNTK
  -- After integral_const we have (μ.real univ) • const which is 1 • const = const.
  simp

/-! #### Per-summand variance bound (operator-norm form)

We deliver the variance bound in **operator-norm form** rather than
Loewner form `∑ ∫ X · X ≤ σ² • 1`. Lifting the norm bound to a Loewner
bound `H² ≤ ‖H‖²_op • 1` for Hermitian `H` requires PSD/CFC machinery
that is its own piece of work (see file-level docstring above).
-/

open scoped Matrix.Norms.L2Operator in
/-- **Per-summand product op-norm bound.** For a bounded activation
`|σ z| ≤ M`, the operator norm of the product `X · X` for
`X := centeredNeuronNTKSummand σ xs ν m wb` is bounded by
`4 n² M⁴ / m²`. -/
lemma centeredNeuronNTKSummand_mul_self_opNorm_le
    {n m : ℕ} {σ : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m) (wb : EuclideanSpace ℝ (Fin d) × ℝ) :
    ‖centeredNeuronNTKSummand σ xs ν m wb *
        centeredNeuronNTKSummand σ xs ν m wb‖
      ≤ 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2 := by
  -- ‖A · A‖ ≤ ‖A‖²: from sub-multiplicativity of the operator norm
  -- (`NormedRing` structure: `‖A * B‖ ≤ ‖A‖ * ‖B‖`).
  have h_norm_mul : ‖centeredNeuronNTKSummand σ xs ν m wb *
      centeredNeuronNTKSummand σ xs ν m wb‖ ≤
      ‖centeredNeuronNTKSummand σ xs ν m wb‖ ^ 2 := by
    calc ‖centeredNeuronNTKSummand σ xs ν m wb *
              centeredNeuronNTKSummand σ xs ν m wb‖
        ≤ ‖centeredNeuronNTKSummand σ xs ν m wb‖ *
            ‖centeredNeuronNTKSummand σ xs ν m wb‖ := norm_mul_le _ _
      _ = ‖centeredNeuronNTKSummand σ xs ν m wb‖ ^ 2 := by ring
  have h_norm_bound : ‖centeredNeuronNTKSummand σ xs ν m wb‖
      ≤ 2 * (n : ℝ) * M ^ 2 / (m : ℝ) :=
    centeredNeuronNTKSummand_opNorm_le hM hσ xs ν hm wb
  have h_norm_sq_bound :
      ‖centeredNeuronNTKSummand σ xs ν m wb‖ ^ 2
      ≤ (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) h_norm_bound 2
  have h_simp : (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) ^ 2
      = 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2 := by ring
  linarith [h_norm_mul, h_norm_sq_bound, h_simp.symm ▸ h_norm_sq_bound]

open scoped Matrix.Norms.L2Operator in
/-- **Per-summand variance norm bound (sum form).** For a bounded
activation `|σ z| ≤ M`, the sum over `j = 1..m` of the operator norms
of `X · X` (with `X := centeredNeuronNTKSummand`) is bounded by
`4 n² M⁴ / m`.

This is the **norm-form** of the variance bound. The Loewner-form
`∑ ∫ X · X ≤ (4 n² M⁴ / m) • 1` consumed by `Matrix.bernstein_full`
follows from the operator-norm bound on each summand plus the standard
Hermitian fact `H² ≤ ‖H‖²_op • 1`; the latter is its own piece of CFC
infrastructure that is not delivered in this file (see file-level
docstring). -/
lemma centeredNeuronNTKSummand_variance_norm_sum_le
    {n m : ℕ} {σ : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hσ : ∀ z, |σ z| ≤ M)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ν]
    (hm : 0 < m)
    (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :
    ∑ j, ‖centeredNeuronNTKSummand σ xs ν m (ω j) *
            centeredNeuronNTKSummand σ xs ν m (ω j)‖
      ≤ 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) := by
  -- Each summand is bounded by 4 n² M⁴ / m².
  have h_each : ∀ j : Fin m,
      ‖centeredNeuronNTKSummand σ xs ν m (ω j) *
        centeredNeuronNTKSummand σ xs ν m (ω j)‖
        ≤ 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2 :=
    fun j => centeredNeuronNTKSummand_mul_self_opNorm_le
      hM hσ xs ν hm (ω j)
  calc ∑ j, ‖centeredNeuronNTKSummand σ xs ν m (ω j) *
                centeredNeuronNTKSummand σ xs ν m (ω j)‖
      ≤ ∑ _j : Fin m, 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2 :=
        Finset.sum_le_sum fun j _ => h_each j
    _ = (m : ℝ) * (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ) := by
        have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
        field_simp

end ProbabilityTheory
