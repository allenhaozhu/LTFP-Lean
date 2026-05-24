/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.GaussianPosteriorKernel
import LTFP.MathlibExt.Probability.Distributions.JointPriorObservationSndIsMultivariateGaussian

/-!
# The Gaussian posterior compProd is the pushforward of an independent product

The composition-product `multivariateGaussian 0 obsCov ⊗ₘ gaussianPosteriorKernel`
equals the pushforward of the *independent* product of the observation
Gaussian and the (zero-mean) Schur posterior Gaussian through the
affine "posterior joint" map `(y, ε) ↦ (y, K · y + ε)`, where
`K = priorCov · Xᵀ · obsCov⁻¹` is the posterior gain matrix.

This is the structural bridge that lets us identify the
`(observation, posterior)` joint law as Gaussian, which in turn feeds
the B4 N2 carrier closure (`gaussianPosteriorMean_ridge_form`).

Modelled directly on `jointPriorObservation_eq_map_prod`: we swap the
roles of dimensions (`Fin n` on the first coordinate, `Fin d` on the
second), replace the design matrix `X` with the posterior gain matrix,
and replace the noise Gaussian with the Schur posterior Gaussian.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace ProbabilityTheory

/-! ### Markov / S-finite instances for `gaussianPosteriorKernel`

The composition-product `μ ⊗ₘ κ` requires `κ` to be an `IsSFiniteKernel`
to make `Measure.compProd_apply` available. We supply the chain
`IsProbabilityMeasure ⇒ IsMarkovKernel ⇒ IsSFiniteKernel`. -/

instance instIsProbabilityMeasureGaussianPosteriorKernel
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (hPost : (Matrix.schurPosteriorCov priorCov X (ν ^ 2)).PosSemidef)
    (y : EuclideanSpace ℝ (Fin n)) :
    IsProbabilityMeasure (gaussianPosteriorKernel priorCov X ν hPost y) := by
  rw [gaussianPosteriorKernel_apply]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance instIsMarkovKernelGaussianPosteriorKernel
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (hPost : (Matrix.schurPosteriorCov priorCov X (ν ^ 2)).PosSemidef) :
    IsMarkovKernel (gaussianPosteriorKernel priorCov X ν hPost) :=
  ⟨fun _ => instIsProbabilityMeasureGaussianPosteriorKernel priorCov X ν hPost _⟩

instance instIsSFiniteKernelGaussianPosteriorKernel
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (hPost : (Matrix.schurPosteriorCov priorCov X (ν ^ 2)).PosSemidef) :
    IsSFiniteKernel (gaussianPosteriorKernel priorCov X ν hPost) :=
  inferInstance

instance instIsGaussianGaussianPosteriorKernelFiber
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (hPost : (Matrix.schurPosteriorCov priorCov X (ν ^ 2)).PosSemidef)
    (y : EuclideanSpace ℝ (Fin n)) :
    IsGaussian (gaussianPosteriorKernel priorCov X ν hPost y) := by
  rw [gaussianPosteriorKernel_apply]
  infer_instance

/-! ### The posterior joint map and the `compProd = map_prod` identity -/

/-- The **posterior joint map** `Φ : E_n × E_d → E_n × E_d` defined by
`Φ (y, ε) = (y, K · y + ε)`, where `K = priorCov · Xᵀ · obsCov⁻¹` is the
posterior gain matrix. The identity on the first coordinate and an
affine reparametrisation on the second, exactly mirroring the
`observationJointMap` but with the roles of the two coordinates
swapped and the design matrix `X` replaced by the gain matrix. -/
noncomputable def posteriorJointMap
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin d))).prod
    ((regressionCLM (priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹)).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℝ (Fin d)))
      + ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℝ (Fin d)))

@[simp] lemma posteriorJointMap_apply
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :
    posteriorJointMap priorCov X ν p =
      (p.1,
        regressionCLM (priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹)
          p.1 + p.2) := rfl

/-- The key identity: the composition-product of the observation
Gaussian and the Gaussian posterior kernel equals the pushforward of
the independent product `obsGauss ⊗ schurPostGauss` through the
posterior joint map `(y, ε) ↦ (y, K · y + ε)`. -/
theorem gaussianPosteriorKernel_compProd_eq_map_prod
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (hObs : (Matrix.obsCov priorCov X (ν ^ 2)).PosSemidef)
    (hPost : (Matrix.schurPosteriorCov priorCov X (ν ^ 2)).PosSemidef) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
          (Matrix.obsCov priorCov X (ν ^ 2)) hObs
        ⊗ₘ gaussianPosteriorKernel priorCov X ν hPost
      = ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
            (Matrix.obsCov priorCov X (ν ^ 2)) hObs).prod
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
            (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost)).map
            (posteriorJointMap priorCov X ν) := by
  classical
  ext s hs
  set obsMeas : Measure (EuclideanSpace ℝ (Fin n)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      (Matrix.obsCov priorCov X (ν ^ 2)) hObs with hObsMeas
  set postMeas : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost with hPostMeas
  rw [Measure.compProd_apply hs]
  -- Rewrite posterior kernel fiber via gaussianPosteriorKernel_apply.
  have hker : ∀ y : EuclideanSpace ℝ (Fin n),
      (gaussianPosteriorKernel priorCov X ν hPost y) (Prod.mk y ⁻¹' s)
        = postMeas ((fun ε =>
              regressionCLM
                (priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹) y + ε)
            ⁻¹' (Prod.mk y ⁻¹' s)) := by
    intro y
    rw [gaussianPosteriorKernel_apply]
    rw [Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  simp_rw [hker]
  -- RHS: map by Φ, prod measure.
  have hΦ : Measurable (posteriorJointMap priorCov X ν) :=
    (posteriorJointMap priorCov X ν).continuous.measurable
  rw [Measure.map_apply hΦ hs]
  rw [Measure.prod_apply (hΦ hs)]
  -- Both inner sets are equal: `posteriorJointMap (y, ε) = (y, K · y + ε)`,
  -- so `Prod.mk y ⁻¹' (Φ ⁻¹' s) = (fun ε => K · y + ε) ⁻¹' (Prod.mk y ⁻¹' s)`.
  rfl

/-- The composition-product of the observation Gaussian and the
Gaussian posterior kernel is itself **Gaussian**. Follows immediately
from the pushforward identity above plus `IsGaussian.prod` and the
CLM-pushforward instance for `posteriorJointMap`. -/
instance instIsGaussianGaussianPosteriorKernelCompProd
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (hObs : (Matrix.obsCov priorCov X (ν ^ 2)).PosSemidef)
    (hPost : (Matrix.schurPosteriorCov priorCov X (ν ^ 2)).PosSemidef) :
    IsGaussian
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
            (Matrix.obsCov priorCov X (ν ^ 2)) hObs
          ⊗ₘ gaussianPosteriorKernel priorCov X ν hPost) := by
  rw [gaussianPosteriorKernel_compProd_eq_map_prod]
  have hObsG : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      (Matrix.obsCov priorCov X (ν ^ 2)) hObs) := inferInstance
  have hPostG : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost) := inferInstance
  infer_instance

end ProbabilityTheory
