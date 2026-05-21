/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev

/-!
# `l₂` operator norm of a square matrix is bounded by `card × entrywise sup`

For a square matrix `A : Matrix n n ℝ` with all entries bounded in
norm by some constant `s ≥ 0`, the `l²` operator (spectral) norm
`‖A‖` (under the scoped `Matrix.Norms.L2Operator` instance) is
bounded by

  `‖A‖ ≤ (Fintype.card n) · s`.

This is a loose but elementary bound, obtained by applying the
scalar Cauchy–Schwarz inequality
(`Finset.sq_sum_le_card_mul_sum_sq`) entrywise.

It is the glue lemma needed by the empirical-NTK scalar-Hoeffding
concentration argument
(`LTFP/MathlibExt/Probability/NTKConcentration.lean`).
Mathlib has the intermediate norms — Frobenius, elementwise sup,
`l²` operator — but no direct connector between the `l²` operator
norm and the elementwise sup. We supply that connector here.

## Main result

* `Matrix.l2_opNorm_le_card_mul_of_entry_le` :
  `(∀ i j, ‖A i j‖ ≤ s) → ‖A‖ ≤ (Fintype.card n) · s`.
-/

namespace Matrix

open scoped Matrix.Norms.L2Operator BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a real square matrix `A` whose entries are all bounded by
`s ≥ 0`, the `l²` operator (spectral) norm is bounded by
`(Fintype.card n) * s`.

The proof goes through `Matrix.toEuclideanCLM` and applies
the Cauchy–Schwarz scalar inequality
(`Finset.sq_sum_le_card_mul_sum_sq`) once per row. -/
theorem l2_opNorm_le_card_mul_of_entry_le (A : Matrix n n ℝ)
    {s : ℝ} (hs : 0 ≤ s) (h_entry : ∀ i j : n, ‖A i j‖ ≤ s) :
    ‖A‖ ≤ (Fintype.card n : ℝ) * s := by
  -- Reduce to the continuous linear map.
  rw [← l2_opNorm_toEuclideanCLM]
  -- Set `M := card n · s`.
  set M : ℝ := (Fintype.card n : ℝ) * s with hM_def
  have hcard_nat : 0 ≤ (Fintype.card n : ℝ) := by exact_mod_cast Nat.zero_le _
  have hM_nonneg : 0 ≤ M := mul_nonneg hcard_nat hs
  -- Each `‖A i j‖^2` is at most `s^2`.
  have h_entry_sq : ∀ i j : n, A i j ^ 2 ≤ s ^ 2 := by
    intro i j
    have h := h_entry i j
    -- `‖A i j‖ = |A i j|` and `0 ≤ ‖A i j‖`.
    have habs : |A i j| ≤ s := by simpa [Real.norm_eq_abs] using h
    have h_sq : A i j ^ 2 = |A i j| ^ 2 := by rw [sq_abs]
    rw [h_sq]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  -- Apply the CLM operator-norm bound.
  refine ContinuousLinearMap.opNorm_le_bound _ hM_nonneg ?_
  intro x
  -- Identify the CLM action with the matrix-vector product.
  have hAct :
      toEuclideanCLM (n := n) (𝕜 := ℝ) A x =
        (EuclideanSpace.equiv n ℝ).symm
          (A *ᵥ ((EuclideanSpace.equiv n ℝ) x)) := rfl
  set y : n → ℝ := EuclideanSpace.equiv n ℝ x with hy_def
  -- It suffices to bound the squared norms.
  have hM_x_nonneg : 0 ≤ M * ‖x‖ := mul_nonneg hM_nonneg (norm_nonneg _)
  have h_target_sq :
      ‖toEuclideanCLM (n := n) (𝕜 := ℝ) A x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [hAct]
    rw [EuclideanSpace.norm_sq_eq, mul_pow]
    -- LHS reduces to ∑ i, ‖(A *ᵥ y) i‖²
    -- but the `EuclideanSpace.equiv.symm` introduces an `ofLp` wrap.
    have h_lhs :
        ∑ i, ‖((EuclideanSpace.equiv n ℝ).symm (A *ᵥ y)) i‖ ^ 2
        = ∑ i, ‖(A *ᵥ y) i‖ ^ 2 := rfl
    rw [h_lhs]
    -- ‖x‖² = ∑ j, ‖y j‖² by the EuclideanSpace identity.
    have h_x_sq : ‖x‖ ^ 2 = ∑ j, ‖y j‖ ^ 2 := EuclideanSpace.norm_sq_eq x
    rw [h_x_sq]
    -- Pointwise bound: ‖(A *ᵥ y) i‖² ≤ n · s² · ∑ j, ‖y j‖².
    have h_pointwise : ∀ i : n,
        ‖(A *ᵥ y) i‖ ^ 2 ≤ (Fintype.card n : ℝ) * s ^ 2 * ∑ j, ‖y j‖ ^ 2 := by
      intro i
      -- (A *ᵥ y) i = ∑ j, A i j * y j
      have h_mulvec : (A *ᵥ y) i = ∑ j, A i j * y j := by
        simp [Matrix.mulVec, dotProduct]
      -- |∑ j, A i j · y j|² ≤ card n · ∑ j, |A i j · y j|² ≤ card n · ∑ j, s² · y_j²
      have h_step1 : (∑ j, A i j * y j) ^ 2 ≤
          (Fintype.card n : ℝ) * ∑ j, (A i j * y j) ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset n))
          (f := fun j => A i j * y j)
        simpa [Finset.card_univ] using this
      have h_step2 : ∀ j, (A i j * y j) ^ 2 ≤ s ^ 2 * y j ^ 2 := by
        intro j
        have h1 : (A i j * y j) ^ 2 = A i j ^ 2 * y j ^ 2 := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right (h_entry_sq i j) (sq_nonneg _)
      have h_step3 : ∑ j, (A i j * y j) ^ 2 ≤ ∑ j, s ^ 2 * y j ^ 2 :=
        Finset.sum_le_sum fun j _ => h_step2 j
      have h_step4 : ∑ j, s ^ 2 * y j ^ 2 = s ^ 2 * ∑ j, y j ^ 2 := by
        rw [← Finset.mul_sum]
      calc ‖(A *ᵥ y) i‖ ^ 2
          = (∑ j, A i j * y j) ^ 2 := by rw [h_mulvec, Real.norm_eq_abs, sq_abs]
        _ ≤ (Fintype.card n : ℝ) * ∑ j, (A i j * y j) ^ 2 := h_step1
        _ ≤ (Fintype.card n : ℝ) * (s ^ 2 * ∑ j, y j ^ 2) := by
            gcongr
            rw [← h_step4]; exact h_step3
        _ = (Fintype.card n : ℝ) * s ^ 2 * ∑ j, ‖y j‖ ^ 2 := by
            simp only [Real.norm_eq_abs, sq_abs]; ring
    -- Sum the pointwise estimates over i.
    calc ∑ i, ‖(A *ᵥ y) i‖ ^ 2
        ≤ ∑ _i : n, (Fintype.card n : ℝ) * s ^ 2 * ∑ j, ‖y j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => h_pointwise i
      _ = (Fintype.card n : ℝ) * ((Fintype.card n : ℝ) * s ^ 2 * ∑ j, ‖y j‖ ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ]; ring
      _ = M ^ 2 * ∑ j, ‖y j‖ ^ 2 := by rw [hM_def]; ring
  -- From squared bound, deduce the bound on norms.
  exact le_of_sq_le_sq h_target_sq hM_x_nonneg

end Matrix
