/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Ridge algebraic identity

A small algebraic identity for the regularized matrix inverse,
`(M + ρ·I)⁻¹ · M = I - ρ · (M + ρ·I)⁻¹`, useful as one step in the
Gaussian conjugate-prior posterior-mean derivation (Bach 2024 §3.7).

This is NOT the full Gaussian conjugate-prior identity (which requires
the measure-theoretic conditional-expectation infrastructure that
Mathlib does not yet have). It is one of the algebraic substitutions
the conjugacy proof would use.
-/

open Matrix

namespace LTFP.MathlibExt.LinearAlgebra

noncomputable section

/-- Algebraic ridge identity: `(M + ρ·I)⁻¹ · M = I - ρ · (M + ρ·I)⁻¹`. -/
theorem Matrix.regularized_inv_mul_eq_one_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (rho : ℝ)
    (hM : IsUnit (M + rho • (1 : Matrix ι ι ℝ)).det) :
    (M + rho • (1 : Matrix ι ι ℝ))⁻¹ * M
      = (1 : Matrix ι ι ℝ) - rho • (M + rho • (1 : Matrix ι ι ℝ))⁻¹ := by
  classical
  let B : Matrix ι ι ℝ := M + rho • (1 : Matrix ι ι ℝ)
  have hB : IsUnit B.det := by simpa [B] using hM
  have hM' : M = B - rho • (1 : Matrix ι ι ℝ) := by
    simp [B]
  calc
    B⁻¹ * M = B⁻¹ * (B - rho • (1 : Matrix ι ι ℝ)) := by rw [hM']
    _ = B⁻¹ * B - B⁻¹ * (rho • (1 : Matrix ι ι ℝ)) := by rw [Matrix.mul_sub]
    _ = (1 : Matrix ι ι ℝ) - rho • B⁻¹ := by
      rw [Matrix.nonsing_inv_mul B hB]
      simp

end

end LTFP.MathlibExt.LinearAlgebra
