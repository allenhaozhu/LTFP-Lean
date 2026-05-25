/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import LTFP.MathlibExt.Probability.NTKConcentration
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

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

end ProbabilityTheory
