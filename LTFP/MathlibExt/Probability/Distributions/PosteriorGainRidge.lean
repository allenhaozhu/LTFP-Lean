/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.GaussianPosteriorCovariancesPositive

/-!
# Posterior gain matrix in ridge form

Woodbury push-through identity: the posterior gain
`priorCov · Xᵀ · (X · priorCov · Xᵀ + ν²·I)⁻¹` equals the ridge form
`(Xᵀ · X + ν² · priorCov⁻¹)⁻¹ · Xᵀ`. Sub-step toward the B4 N2 carrier
closure (gaussianPosteriorMean_ridge_form).
-/

open scoped Matrix

theorem posteriorGain_eq_ridge
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosDef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (hν : ν ≠ 0) :
    priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹ =
      (Xᵀ * X + ν ^ 2 • priorCov⁻¹)⁻¹ * Xᵀ := by
  classical
  have hPriorDet : IsUnit priorCov.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hPrior.isUnit
  have hGram : (Xᵀ * X).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X
  have hRegularizer : (ν ^ 2 • priorCov⁻¹).PosDef :=
    Matrix.PosDef.smul hPrior.inv (sq_pos_of_ne_zero hν)
  have hRidge : (Xᵀ * X + ν ^ 2 • priorCov⁻¹).PosDef :=
    Matrix.PosDef.posSemidef_add hGram hRegularizer
  have hRidgeDet : IsUnit (Xᵀ * X + ν ^ 2 • priorCov⁻¹).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hRidge.isUnit
  have hObs : (Matrix.obsCov priorCov X (ν ^ 2)).PosDef :=
    (gaussianPosterior_covariances_pos priorCov hPrior X ν hν).1
  have hObsDet : IsUnit (Matrix.obsCov priorCov X (ν ^ 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hObs.isUnit
  have hkey :
      (Xᵀ * X + ν ^ 2 • priorCov⁻¹) * (priorCov * Xᵀ) =
        Xᵀ * Matrix.obsCov priorCov X (ν ^ 2) := by
    unfold Matrix.obsCov
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      ← Matrix.mul_assoc priorCov⁻¹ priorCov Xᵀ,
      Matrix.nonsing_inv_mul _ hPriorDet, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  calc
    priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹ =
        (Xᵀ * X + ν ^ 2 • priorCov⁻¹)⁻¹ *
          ((Xᵀ * X + ν ^ 2 • priorCov⁻¹) * (priorCov * Xᵀ)) *
          (Matrix.obsCov priorCov X (ν ^ 2))⁻¹ := by
      rw [← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hRidgeDet, Matrix.one_mul]
    _ = (Xᵀ * X + ν ^ 2 • priorCov⁻¹)⁻¹ *
          (Xᵀ * Matrix.obsCov priorCov X (ν ^ 2)) *
          (Matrix.obsCov priorCov X (ν ^ 2))⁻¹ := by
      rw [hkey]
    _ = (Xᵀ * X + ν ^ 2 • priorCov⁻¹)⁻¹ * Xᵀ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hObsDet, Matrix.mul_one]
