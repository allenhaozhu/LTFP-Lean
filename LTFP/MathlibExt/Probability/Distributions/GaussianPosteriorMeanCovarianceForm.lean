/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.GaussianPosteriorCompProdEqSwappedJoint
import Mathlib.Probability.Kernel.Posterior

/-!
# Gaussian posterior mean in covariance form (B4 N2 I5)

The covariance-form posterior mean identity for the Gaussian conjugate-prior
setup. The Mathlib posterior kernel `κ†μ` of the Gaussian observation kernel
`κ = gaussianObservationKernel X ν` relative to the prior
`μ = multivariateGaussian 0 priorCov` is, almost surely with respect to the
observation marginal `κ ∘ₘ μ`, equal to the explicit Gaussian posterior
kernel built in `GaussianPosteriorKernel.lean`. Pushing this a.e. equality
through the vector integral yields the Bach (2024) Eq. 7.21 identity

```
𝔼[θ ∣ y] = priorCov · Xᵀ · obsCov⁻¹ · y
```

for `(κ ∘ₘ μ)`-almost every observation `y`. This composes the explicit
fiber integral (I3, `gaussianPosteriorKernel_integral_vector`) with the
compProd identity (I4, `gaussianPosteriorKernel_compProd_eq_swapped_joint`)
via `ProbabilityTheory.ae_eq_posterior_of_compProd_eq`.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace ProbabilityTheory

/-- **B4 N2 I5.** The covariance-form Gaussian posterior mean identity.

For the Gaussian linear-regression observation kernel
`κ = gaussianObservationKernel X ν` and the Gaussian prior
`μ = multivariateGaussian 0 priorCov`, the posterior mean equals the
linear "gain matrix times observation" expression
`priorCov · Xᵀ · obsCov⁻¹ · y`, almost surely with respect to the
observation marginal `κ ∘ₘ μ`.

This is Bach (2024) *Learning Theory from First Principles*, Eq. 7.21,
the closed-form Bayesian estimator for Gaussian conjugate priors. -/
theorem gaussianPosteriorMean_covariance_form
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosDef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (hν : ν ≠ 0) :
    ∀ᵐ y ∂(gaussianObservationKernel X ν ∘ₘ
        multivariateGaussian 0 priorCov hPrior.posSemidef),
      ∫ θ, θ ∂((gaussianObservationKernel X ν)†
          (multivariateGaussian 0 priorCov hPrior.posSemidef)) y =
        regressionCLM
          (priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹) y := by
  classical
  set μ : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian 0 priorCov hPrior.posSemidef with hμ_def
  set κ : Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)) :=
    gaussianObservationKernel X ν with hκ_def
  set η : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin d)) :=
    gaussianPosteriorKernel priorCov X ν
      (gaussianPosterior_covariances_pos priorCov hPrior X ν hν).2 with hη_def
  -- The explicit posterior kernel η agrees, almost surely, with the
  -- Mathlib posterior κ†μ. This is the bridge lemma
  -- `ae_eq_posterior_of_compProd_eq`, whose equation hypothesis is
  -- precisely the I4 identity once we rewrite the second marginal.
  have hη : η =ᵐ[κ ∘ₘ μ] κ†μ := by
    refine ae_eq_posterior_of_compProd_eq ?_
    -- The hypothesis: `(κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap`. After
    -- identifying `κ ∘ₘ μ` with the joint's second marginal and
    -- `μ ⊗ₘ κ` with the joint itself, this is exactly I4.
    have hSnd : (jointPriorObservation priorCov hPrior.posSemidef X ν).snd
        = κ ∘ₘ μ := by
      simpa [hκ_def, hμ_def] using
        jointPriorObservation_snd priorCov hPrior.posSemidef X ν
    have hJoint : jointPriorObservation priorCov hPrior.posSemidef X ν
        = μ ⊗ₘ κ := rfl
    -- Rewrite I4 into the shape required by ae_eq_posterior_of_compProd_eq.
    have hI4 := gaussianPosteriorKernel_compProd_eq_swapped_joint
      priorCov hPrior X ν hν
    rw [hSnd, hJoint] at hI4
    exact hI4
  -- Now push the a.e. equality through the integral.
  filter_upwards [hη] with y hy
  -- Goal: ∫ θ, θ ∂(κ†μ y) = regressionCLM (...) y. Use ← hy to
  -- replace the integrand on the LHS by the explicit fiber.
  rw [← hy]
  exact gaussianPosteriorKernel_integral_vector priorCov X ν _ y

end ProbabilityTheory
