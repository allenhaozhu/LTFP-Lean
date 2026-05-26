/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianMeasure

/-!
# Multivariate Gaussian mean-squared error

Proposed Mathlib path: `Mathlib/Statistics/MultivariateGaussianMSE.lean`.
Proposed Mathlib namespace: `Statistics`.

This module lands the **general-`d` Gaussian mean-squared error**, a
direct generalization of the d=1 `gaussianMSED1`. For a measurable
estimator
`A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)`, parameter
`θ : EuclideanSpace ℝ (Fin d)`, and noise scale `σ : ℝ`,

  `gaussianMSEGeneralD A θ σ =
     ∫ x, ‖A x - θ‖² ∂(multivariateGaussian θ (σ²·I))`.

This is the concrete instantiation of the abstract `excessRisk` used in
the closure of the OLS minimax lower bound at general `d` (Bach 2024,
§3.7; Tsybakov 2009, §2.4.2).

## Main definitions

* `Statistics.gaussianMSEGeneralD A θ σ` — the Gaussian MSE of an
  estimator `A` at true parameter `θ` under multivariate Gaussian
  sampling with diagonal covariance `σ²·I`.

## Main results

* `Statistics.gaussianMSEGeneralD_nonneg` — the MSE is nonnegative for
  any estimator (integral of nonneg integrand).

## References

* F. Bach, *Learning Theory from First Principles*, MIT Press, 2024,
  §3.7 (Mourtada minimax lower bound for OLS).
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, §2.4.2 (two-point method, squared-loss form).

## Tags

OLS, minimax, lower bound, two-point method, Gaussian, MSE,
multivariate
-/

namespace LTFP.MathlibExt.Probability

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-- The **multivariate Gaussian mean-squared error** of an estimator
`A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)` at parameter
`θ : EuclideanSpace ℝ (Fin d)` and noise scale `σ : ℝ`:

`gaussianMSEGeneralD A θ σ = ∫ x, ‖A x - θ‖² ∂(N(θ, σ²·I))`.

This is the concrete instantiation of the abstract `excessRisk` used in
the closure of `ols_minimax_lower_bound_general_d_gaussian` at general
`d`. The covariance `σ²·I` is the canonical isotropic noise covariance
for the d=1 sample-mean reduction generalized to vector-valued
estimators. -/
noncomputable def gaussianMSEGeneralD
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (σ : ℝ) : ℝ :=
  ∫ x, ‖A x - θ‖^2 ∂(multivariateGaussian θ ((σ^2) • (1 : Matrix (Fin d) (Fin d) ℝ))
        (posSemidef_sq_smul_one (n := d) σ))

/-- The multivariate Gaussian MSE is nonnegative for any estimator: it
is the integral of the pointwise-nonnegative function `‖A x - θ‖²`. -/
theorem gaussianMSEGeneralD_nonneg
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (σ : ℝ) :
    0 ≤ gaussianMSEGeneralD A θ σ := by
  unfold gaussianMSEGeneralD
  apply integral_nonneg
  intro y
  exact sq_nonneg _

end LTFP.MathlibExt.Probability
