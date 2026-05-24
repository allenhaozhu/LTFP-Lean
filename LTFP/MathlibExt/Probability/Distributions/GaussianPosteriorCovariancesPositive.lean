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

/-- Matrix-algebra bridge for the Sub-I4.D `(θ, θ)`-block computation:
the conjugation `K · S · Kᵀ` of the observation covariance by the
Kalman-gain matrix `K = priorCov · Xᵀ · S⁻¹` collapses to the closed
form `priorCov · Xᵀ · S⁻¹ · X · priorCov`. Uses symmetry of `priorCov`
and `S` (both are positive-definite, hence Hermitian; over `ℝ`,
Hermitian equals transpose) plus the cancellation `S * S⁻¹ = 1`. -/
theorem K_S_Ktrans_eq_priorCov_Xtrans_Sinv_X_priorCov
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosDef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (hν : ν ≠ 0) :
    let S := Matrix.obsCov priorCov X (ν ^ 2)
    let K := priorCov * Xᵀ * S⁻¹
    K * S * Kᵀ = priorCov * Xᵀ * S⁻¹ * (X * priorCov) := by
  classical
  -- Obtain positive-definiteness of `S` from the covariance positivity lemma.
  obtain ⟨hS, _⟩ :=
    gaussianPosterior_covariances_pos priorCov hPrior X ν hν
  set S : Matrix (Fin n) (Fin n) ℝ := Matrix.obsCov priorCov X (ν ^ 2) with hSdef
  -- `S` is a unit (its determinant is a unit).
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).1 hS.isUnit
  -- Symmetry of `priorCov` and `S` (Hermitian over `ℝ` collapses to transpose).
  have hPriorSymm : priorCovᵀ = priorCov := by
    have h := hPrior.isHermitian.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hSsymm : Sᵀ = S := by
    have h := hS.isHermitian.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  -- Compute `Kᵀ`. With `K = priorCov * Xᵀ * S⁻¹`,
  -- `Kᵀ = (S⁻¹)ᵀ * X * priorCovᵀ = S⁻¹ * X * priorCov`.
  have hSinvT : (S⁻¹)ᵀ = S⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hSsymm]
  -- Expand the goal and use associativity to expose `S⁻¹ * S = 1`.
  show priorCov * Xᵀ * S⁻¹ * S * (priorCov * Xᵀ * S⁻¹)ᵀ
      = priorCov * Xᵀ * S⁻¹ * (X * priorCov)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hSinvT,
      Matrix.transpose_transpose, hPriorSymm]
  -- Goal:
  --   priorCov * Xᵀ * S⁻¹ * S * (S⁻¹ * X * priorCov)
  -- = priorCov * Xᵀ * S⁻¹ * (X * priorCov)
  rw [Matrix.mul_assoc (priorCov * Xᵀ) S⁻¹ S,
      Matrix.nonsing_inv_mul S hSdet, Matrix.mul_one,
      ← Matrix.mul_assoc (priorCov * Xᵀ) S⁻¹ (X * priorCov)]
