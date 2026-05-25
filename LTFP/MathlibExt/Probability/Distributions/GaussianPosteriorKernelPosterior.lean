/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.GaussianPosteriorCompProdEqSwappedJoint
import Mathlib.Probability.Kernel.Posterior

/-!
# Identification of the Gaussian posterior kernel with Mathlib's `posterior`

The explicit Gaussian posterior kernel `gaussianPosteriorKernel` (built in
`GaussianPosteriorKernel.lean`) agrees, almost surely with respect to the
observation marginal, with the abstract Mathlib `posterior` kernel
`(gaussianObservationKernel X ν)†(multivariateGaussian 0 priorCov)`.

This is a clean, public restatement of the bridge step internally used in
`GaussianPosteriorMeanCovarianceForm.lean`. It is the smallest reusable
fact downstream callers need when they want to work with the Mathlib
posterior abstraction but still benefit from the explicit Gaussian
construction.

The proof composes Mathlib's posterior uniqueness lemma
`ae_eq_posterior_of_compProd_eq` with the local marginal identity
`jointPriorObservation_snd` and the Sub-I4.D identity
`gaussianPosteriorKernel_compProd_eq_swapped_joint`.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace ProbabilityTheory

/-- **Public API.** The explicit Gaussian posterior kernel agrees, almost
surely with respect to the observation marginal, with the abstract Mathlib
`posterior` kernel.

This is the canonical bridge between our explicit `gaussianPosteriorKernel`
(Gaussian with affine mean `priorCov · Xᵀ · obsCov⁻¹ · y` and the Schur
posterior covariance) and Mathlib's abstract `posterior` operator `(·)†(·)`
applied to the Gaussian observation kernel and the centered Gaussian prior.
-/
theorem gaussianPosteriorKernel_ae_eq_posterior
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosDef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (hν : ν ≠ 0) :
    gaussianPosteriorKernel priorCov X ν
        (gaussianPosterior_covariances_pos priorCov hPrior X ν hν).2
      =ᵐ[gaussianObservationKernel X ν ∘ₘ
          multivariateGaussian 0 priorCov hPrior.posSemidef]
        (gaussianObservationKernel X ν)†
          (multivariateGaussian 0 priorCov hPrior.posSemidef) := by
  classical
  set μ : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian 0 priorCov hPrior.posSemidef with hμ_def
  set κ : Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)) :=
    gaussianObservationKernel X ν with hκ_def
  refine ae_eq_posterior_of_compProd_eq ?_
  -- The hypothesis: `(κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap`. After
  -- identifying `κ ∘ₘ μ` with the joint's second marginal and
  -- `μ ⊗ₘ κ` with the joint itself, this is exactly Sub-I4.D.
  have hSnd : (jointPriorObservation priorCov hPrior.posSemidef X ν).snd
      = κ ∘ₘ μ := by
    simpa [hκ_def, hμ_def] using
      jointPriorObservation_snd priorCov hPrior.posSemidef X ν
  have hJoint : jointPriorObservation priorCov hPrior.posSemidef X ν
      = μ ⊗ₘ κ := rfl
  have hI4 := gaussianPosteriorKernel_compProd_eq_swapped_joint
    priorCov hPrior X ν hν
  rw [hSnd, hJoint] at hI4
  exact hI4

end ProbabilityTheory
