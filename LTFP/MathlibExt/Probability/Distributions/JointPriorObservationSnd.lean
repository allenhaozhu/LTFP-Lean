/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianMeasure

/-!
# Joint prior-observation second marginal

For the joint Gaussian prior-observation measure `jointPriorObservation`
(in `MultivariateGaussianMeasure.lean`), the second marginal (observation
distribution) equals the composition of the Gaussian observation kernel
with the multivariate Gaussian prior at mean 0. First two marginal-identity
steps toward B4 Node 2 Gaussian conjugate-prior posterior-mean carrier.
-/

open MeasureTheory ProbabilityTheory

/-- Second marginal of the joint prior-observation measure. -/
theorem jointPriorObservation_snd
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    (jointPriorObservation priorCov hPrior X ν).snd
      = gaussianObservationKernel X ν ∘ₘ
          multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior := by
  unfold jointPriorObservation
  rw [Measure.snd_compProd]

/-- First marginal of the joint prior-observation measure: the prior. -/
theorem jointPriorObservation_fst
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    (jointPriorObservation priorCov hPrior X ν).fst
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior := by
  unfold jointPriorObservation
  rw [Measure.fst_compProd]

/-- The first marginal of the joint prior-observation measure is Gaussian.

The first marginal equals the multivariate Gaussian prior at mean `0`
(by `jointPriorObservation_fst`), whose `IsGaussian` instance is
provided by `instIsGaussianMultivariateGaussian`. -/
instance jointPriorObservation_fst_isGaussian
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    IsGaussian (jointPriorObservation priorCov hPrior X ν).fst := by
  rw [jointPriorObservation_fst]
  infer_instance

/-- Sanity instance: the joint prior–observation measure is a probability
measure. The Gaussian prior is a probability measure and the Gaussian
observation kernel is a Markov kernel (by
`instIsMarkovKernelGaussianObservationKernel`), so `Measure.compProd`
produces a probability measure via Mathlib's typeclass infrastructure. -/
instance jointPriorObservation_isProbabilityMeasure
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    IsProbabilityMeasure (jointPriorObservation priorCov hPrior X ν) := by
  unfold jointPriorObservation
  infer_instance
