/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.GaussianPosteriorCovariancesPositive

/-!
# Gaussian posterior covariance in ridge form

The Schur posterior covariance
`schurPosteriorCov priorCov X (ν^2)`
admits the ridge-regularized closed form
`ν^2 • (Xᵀ * X + ν^2 • priorCov⁻¹)⁻¹`,
matching the `ν^2 (XᵀX + ν² priorCov⁻¹)⁻¹` covariance side of the
standard Gaussian conjugate-prior identity.

The argument composes the Woodbury / precision-form identity
(`schurPosteriorCov_eq_precision_inv_of_obsCov`) with a scalar pull-out:

```
priorCov⁻¹ + Xᵀ · (ν⁻² • 1) · X
  = ν⁻² • (Xᵀ · X + ν² • priorCov⁻¹)
```

inverting both sides and pulling the scalar through `Matrix.inv_eq_left_inv`
yields the claimed ridge form. The development mirrors the mean side
(`posteriorGain_eq_ridge` and `gaussianPosteriorMean_ridge_form`),
giving the second half of the explicit closed-form posterior.
-/

open scoped Matrix

namespace Matrix

/-- **Scalar pull-out across the precision-form Woodbury sum.** Factoring
the scalar `ν⁻²` out of the data-driven precision update yields a sum of
the form `ν⁻² • (Xᵀ · X + ν² • priorCov⁻¹)`. This is the algebraic
core enabling the ridge-form rewrite of the posterior covariance. -/
theorem priorCov_inv_add_information_eq_smul
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (hν : ν ≠ 0) :
    priorCov⁻¹ + Xᵀ * ((ν ^ 2)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) * X
      = (ν ^ 2)⁻¹ • (Xᵀ * X + ν ^ 2 • priorCov⁻¹) := by
  have hν2 : (ν ^ 2) ≠ 0 := pow_ne_zero 2 hν
  have hXform :
      Xᵀ * ((ν ^ 2)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) * X
        = (ν ^ 2)⁻¹ • (Xᵀ * X) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [hXform, smul_add, smul_smul, inv_mul_cancel₀ hν2, one_smul, add_comm]

/-- **Scalar-matrix inverse identity.** For a unit scalar `c` and a unit
matrix `M`, the inverse of `c • M` equals `c⁻¹ • M⁻¹`. -/
theorem inv_smul_of_isUnit
    {p : Type*} [Fintype p] [DecidableEq p]
    (c : ℝ) (hc : c ≠ 0) (M : Matrix p p ℝ) (hM : IsUnit M.det) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hM, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

end Matrix

namespace ProbabilityTheory

/-- **Public API — posterior covariance ridge form.** The Schur posterior
covariance equals the ridge-regularized closed form
`ν^2 • (Xᵀ · X + ν^2 • priorCov⁻¹)⁻¹`.

Composed with `gaussianPosteriorMean_ridge_form`, this is the explicit
ridge-form Gaussian conjugate posterior:

```
posteriorCov = ν² · (XᵀX + ν² · priorCov⁻¹)⁻¹
𝔼[θ ∣ y] = (XᵀX + ν² · priorCov⁻¹)⁻¹ · Xᵀ · y
```

matching the standard form of Bach (2024) *Learning Theory from First
Principles*, §B.4 N2. -/
theorem gaussianPosteriorCov_ridge_form
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosDef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (hν : ν ≠ 0) :
    Matrix.schurPosteriorCov priorCov X (ν ^ 2)
      = ν ^ 2 • (Xᵀ * X + ν ^ 2 • priorCov⁻¹)⁻¹ := by
  classical
  -- Invertibility of the scalar `ν^2`.
  have hν2 : (ν ^ 2) ≠ 0 := pow_ne_zero 2 hν
  have hν2Unit : IsUnit (ν ^ 2) := isUnit_iff_ne_zero.mpr hν2
  have hν2InvNe : (ν ^ 2)⁻¹ ≠ 0 := inv_ne_zero hν2
  -- Positive-definiteness witnesses we'll need for invertibility.
  have hGram : (Xᵀ * X).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X
  have hRegularizer : (ν ^ 2 • priorCov⁻¹).PosDef :=
    Matrix.PosDef.smul hPrior.inv (sq_pos_of_ne_zero hν)
  have hRidge : (Xᵀ * X + ν ^ 2 • priorCov⁻¹).PosDef :=
    Matrix.PosDef.posSemidef_add hGram hRegularizer
  have hRidgeDet : IsUnit (Xᵀ * X + ν ^ 2 • priorCov⁻¹).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hRidge.isUnit
  have hObsPD : (Matrix.obsCov priorCov X (ν ^ 2)).PosDef :=
    (gaussianPosterior_covariances_pos priorCov hPrior X ν hν).1
  -- Compose: Woodbury precision-form rewrite, factor the scalar out, then
  -- invert with the scalar pulling through.
  rw [← Matrix.schurPosteriorCov_eq_precision_inv_of_obsCov
      priorCov X (ν ^ 2) hPrior.isUnit hν2Unit hObsPD.isUnit,
    Matrix.priorCov_inv_add_information_eq_smul priorCov X ν hν,
    Matrix.inv_smul_of_isUnit ((ν ^ 2)⁻¹) hν2InvNe _ hRidgeDet, inv_inv]

end ProbabilityTheory
