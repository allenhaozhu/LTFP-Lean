/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.GaussianConjugatePosteriorSchur
import Mathlib.Analysis.Matrix.Order

/-!
# Positivity of the posterior covariance blocks

For a positive-definite prior covariance and nonzero noise scale, both
the observation covariance `X · priorCov · Xᵀ + ν²·I` and the Schur
posterior covariance are positive-(semi)-definite. Sub-step toward the
B4 N2 carrier (gaussianPosteriorMean_ridge_form).
-/

open scoped Matrix

theorem gaussianPosterior_covariances_pos
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosDef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (hν : ν ≠ 0) :
    (Matrix.obsCov priorCov X (ν ^ 2)).PosDef ∧
    (Matrix.schurPosteriorCov priorCov X (ν ^ 2)).PosSemidef := by
  classical
  have hNoise : ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one (sq_pos_of_ne_zero hν)
  have hDesign : (X * priorCov * Xᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hPrior.posSemidef.mul_mul_conjTranspose_same X
  have hObs : (Matrix.obsCov priorCov X (ν ^ 2)).PosDef := by
    unfold Matrix.obsCov
    exact Matrix.PosDef.posSemidef_add hDesign hNoise
  refine ⟨hObs, ?_⟩
  have hNoiseInv :
      (((ν ^ 2)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ))).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one (inv_pos.mpr (sq_pos_of_ne_zero hν))
  have hInformation :
      (Xᵀ * ((ν ^ 2)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) * X).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hNoiseInv.posSemidef.conjTranspose_mul_mul_same X
  have hPrecision :
      (priorCov⁻¹ + Xᵀ * ((ν ^ 2)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) * X).PosDef :=
    hPrior.inv.add_posSemidef hInformation
  have hPosterior :
      ((priorCov⁻¹ + Xᵀ * ((ν ^ 2)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) * X)⁻¹).PosSemidef :=
    hPrecision.inv.posSemidef
  have hNoiseUnit : IsUnit (ν ^ 2) :=
    isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hν)
  rw [← Matrix.schurPosteriorCov_eq_precision_inv_of_obsCov
      priorCov X (ν ^ 2) hPrior.isUnit hNoiseUnit hObs.isUnit]
  exact hPosterior
