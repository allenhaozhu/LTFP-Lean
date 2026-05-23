/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# `l2_opNorm ≤ frobenius` connector

Direct Cauchy-Schwarz proof that for a square matrix `A : Matrix n n ℝ`,
the spectral (l2 operator) norm is bounded by the Frobenius norm.
-/

open scoped Matrix.Norms.L2Operator BigOperators
open WithLp

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The l2 operator norm is bounded by the Frobenius norm. -/
theorem l2_opNorm_le_frobenius (A : Matrix n n ℝ) :
    ‖A‖ ≤ @norm (Matrix n n ℝ)
      (Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℝ)).toNorm A := by
  rw [← l2_opNorm_toEuclideanCLM]
  let F : ℝ := @norm (Matrix n n ℝ)
    (Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℝ)).toNorm A
  have hF_nonneg : 0 ≤ F := by
    change 0 ≤ ((Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℝ)).toNorm.norm A)
    change 0 ≤ ‖(toLp 2 fun i => toLp 2 fun j => A i j)‖
    exact norm_nonneg _
  have hF_sq : F ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    change ((Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℝ)).toNorm.norm A) ^ 2
        = ∑ i, ∑ j, ‖A i j‖ ^ 2
    change ‖(toLp 2 fun i => toLp 2 fun j => A i j)‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2
    rw [PiLp.norm_sq_eq_of_L2]
    simp [PiLp.norm_sq_eq_of_L2]
  change ‖toEuclideanCLM (n := n) (𝕜 := ℝ) A‖ ≤ F
  refine ContinuousLinearMap.opNorm_le_bound _ hF_nonneg ?_
  intro x
  have h_pointwise : ∀ i : n,
      ‖(A *ᵥ (ofLp x)) i‖ ^ 2 ≤
        (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖(ofLp x : n → ℝ) j‖ ^ 2 := by
    intro i
    have hcs : (∑ j, A i j * (ofLp x : n → ℝ) j) ^ 2 ≤
        (∑ j, (A i j) ^ 2) * ∑ j, ((ofLp x : n → ℝ) j) ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset n))
        (f := fun j => A i j) (g := fun j => (ofLp x : n → ℝ) j)
    calc
      ‖(A *ᵥ (ofLp x)) i‖ ^ 2 = (∑ j, A i j * (ofLp x : n → ℝ) j) ^ 2 := by
        simp [Matrix.mulVec, dotProduct, Real.norm_eq_abs, sq_abs]
      _ ≤ (∑ j, (A i j) ^ 2) * ∑ j, ((ofLp x : n → ℝ) j) ^ 2 := hcs
      _ = (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖(ofLp x : n → ℝ) j‖ ^ 2 := by
        simp [Real.norm_eq_abs, sq_abs]
  have hx_sq : ‖x‖ ^ 2 = ∑ j, ‖(ofLp x : n → ℝ) j‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq x
  have h_sq : ‖toEuclideanCLM (n := n) (𝕜 := ℝ) A x‖ ^ 2 ≤ (F * ‖x‖) ^ 2 := by
    calc
      ‖toEuclideanCLM (n := n) (𝕜 := ℝ) A x‖ ^ 2
          = ∑ i, ‖(A *ᵥ (ofLp x)) i‖ ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]
            rfl
      _ ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖(ofLp x : n → ℝ) j‖ ^ 2 :=
            Finset.sum_le_sum fun i _ => h_pointwise i
      _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖(ofLp x : n → ℝ) j‖ ^ 2 := by
            rw [Finset.sum_mul]
      _ = F ^ 2 * ‖x‖ ^ 2 := by
            rw [← hF_sq, ← hx_sq]
      _ = (F * ‖x‖) ^ 2 := by ring
  exact le_of_sq_le_sq h_sq (mul_nonneg hF_nonneg (norm_nonneg x))

/-- Squared form of `l2_opNorm_le_frobenius`: convenient when chaining
through Cauchy–Schwarz-style inequalities that naturally produce
squared norms. -/
theorem l2_opNorm_sq_le_frobenius_sq (A : Matrix n n ℝ) :
    ‖A‖ ^ 2 ≤ (@norm (Matrix n n ℝ)
      (Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℝ)).toNorm A) ^ 2 := by
  have hF_nonneg : 0 ≤ (@norm (Matrix n n ℝ)
      (Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℝ)).toNorm A) := by
    change 0 ≤ ((Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℝ)).toNorm.norm A)
    change 0 ≤ ‖(WithLp.toLp 2 fun i => WithLp.toLp 2 fun j => A i j)‖
    exact norm_nonneg _
  exact pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_le_frobenius A) 2

/-- Frobenius-norm expansion of `l2_opNorm_sq_le_frobenius_sq`:
the squared spectral norm is bounded by the entrywise sum of squares. -/
theorem l2_opNorm_sq_le_sum_sq_entries (A : Matrix n n ℝ) :
    ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have hF_sq : (@norm (Matrix n n ℝ)
      (Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℝ)).toNorm A) ^ 2
      = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    change ((Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℝ)).toNorm.norm A) ^ 2
        = ∑ i, ∑ j, ‖A i j‖ ^ 2
    change ‖(WithLp.toLp 2 fun i => WithLp.toLp 2 fun j => A i j)‖ ^ 2
        = ∑ i, ∑ j, ‖A i j‖ ^ 2
    rw [PiLp.norm_sq_eq_of_L2]
    simp [PiLp.norm_sq_eq_of_L2]
  calc ‖A‖ ^ 2
      ≤ (@norm (Matrix n n ℝ)
          (Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℝ)).toNorm A) ^ 2 :=
        l2_opNorm_sq_le_frobenius_sq A
    _ = ∑ i, ∑ j, ‖A i j‖ ^ 2 := hF_sq

end Matrix
