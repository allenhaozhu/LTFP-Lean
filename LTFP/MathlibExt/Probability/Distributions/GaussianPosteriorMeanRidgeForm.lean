/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.GaussianPosteriorMeanCovarianceForm
import LTFP.MathlibExt.Probability.Distributions.PosteriorGainRidge

/-!
# Gaussian posterior mean equals ridge regression estimator (B4 N2 carrier closure)

This module composes the covariance-form posterior mean identity
(`gaussianPosteriorMean_covariance_form`, I5) with the Woodbury
push-through identity (`posteriorGain_eq_ridge`, I6) to obtain the
ridge-form Bayesian estimator

```
𝔼[θ ∣ y] = (Xᵀ X + ν² priorCov⁻¹)⁻¹ Xᵀ y
```

for `(κ ∘ₘ μ)`-almost every observation `y`. This is the closing step
of the B4 N2 carrier path: combined with I1–I6, it discharges the full
Gaussian conjugate posterior mean theorem of Bach (2024) §3.7.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace ProbabilityTheory

/-- **B4 N2 carrier closure.** The Gaussian conjugate posterior mean
equals the ridge regression estimator
`(Xᵀ X + ν² priorCov⁻¹)⁻¹ Xᵀ y`, almost surely with respect to the
observation marginal `κ ∘ₘ μ`.

This is the composition of `gaussianPosteriorMean_covariance_form` (I5,
the covariance-form identity for the posterior mean) with
`posteriorGain_eq_ridge` (I6, the Woodbury push-through that rewrites
the gain matrix in ridge form). -/
theorem gaussianPosteriorMean_ridge_form
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosDef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (hν : ν ≠ 0) :
    ∀ᵐ y ∂(gaussianObservationKernel X ν ∘ₘ
        multivariateGaussian 0 priorCov hPrior.posSemidef),
      ∫ θ, θ ∂((gaussianObservationKernel X ν)†
          (multivariateGaussian 0 priorCov hPrior.posSemidef)) y =
        regressionCLM
          ((Xᵀ * X + ν ^ 2 • priorCov⁻¹)⁻¹ * Xᵀ) y := by
  filter_upwards [gaussianPosteriorMean_covariance_form priorCov hPrior X ν hν]
    with y hy
  rw [hy, posteriorGain_eq_ridge priorCov hPrior X ν hν]

end ProbabilityTheory
