/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.GaussianPosteriorKernel
import LTFP.MathlibExt.Probability.Distributions.JointPriorObservationSndIsMultivariateGaussian
import LTFP.MathlibExt.Probability.Distributions.GaussianPosteriorCovariancesPositive
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Prod

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

/-! ### Vector integrals of the joint posterior measures are zero -/

/-- **Sub-I4.B**: Both the posterior compProd measure (on
`E_n × E_d` with the observation as first coordinate and the
posterior as second) and the `Prod.swap` of the joint
prior–observation measure have zero mean (as vectors).

* **LHS** identifies the compProd
  `joint.snd ⊗ₘ gaussianPosteriorKernel` with the pushforward of
  the independent product `obsGauss ⊗ schurPostGauss` through the
  posterior joint map `(y, ε) ↦ (y, K · y + ε)` (Sub-I4.A), then
  applies `ContinuousLinearMap.integral_id_map` together with
  `integral_continuousLinearMap_prod` to split the product
  integral into two zero-mean Gaussian integrals.
* **RHS** rewrites the joint via `jointPriorObservation_eq_map_prod`
  as `(priorGauss ⊗ noiseGauss).map (observationJointMap X)`, then
  combines with `Prod.swap` via `Measure.map_map` to land in the
  same "map of centered Gaussian product through a CLM" pattern. -/
theorem gaussianPosteriorKernel_compProd_integral_vector_eq_zero
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosDef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (hν : ν ≠ 0) :
    ∫ p, p ∂((jointPriorObservation priorCov hPrior.posSemidef X ν).snd ⊗ₘ
        gaussianPosteriorKernel priorCov X ν
          (gaussianPosterior_covariances_pos priorCov hPrior X ν hν).2) =
      (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) ∧
    ∫ p, p ∂((jointPriorObservation priorCov hPrior.posSemidef X ν).map Prod.swap) =
      (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) := by
  classical
  -- Common setup: posSemidef versions of both block covariances.
  obtain ⟨hObsPD, hPost⟩ :=
    gaussianPosterior_covariances_pos priorCov hPrior X ν hν
  have hObs : (Matrix.obsCov priorCov X (ν ^ 2)).PosSemidef := hObsPD.posSemidef
  -- Set abbreviations for the two Gaussian factor measures used on both
  -- branches.
  set obsGauss : Measure (EuclideanSpace ℝ (Fin n)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      (Matrix.obsCov priorCov X (ν ^ 2)) hObs with hObsGauss
  set postGauss : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost with hPostGauss
  set priorGauss : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior.posSemidef
    with hPriorGauss
  set noiseGauss : Measure (EuclideanSpace ℝ (Fin n)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
      (posSemidef_sq_smul_one (n := n) ν) with hNoiseGauss
  -- Gaussian instances (so `IsGaussian.integrable_id` and product
  -- helpers fire automatically).
  have hObsG : IsGaussian obsGauss := by
    show IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      (Matrix.obsCov priorCov X (ν ^ 2)) hObs)
    infer_instance
  have hPostG : IsGaussian postGauss := by
    show IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost)
    infer_instance
  have hPriorG : IsGaussian priorGauss := by
    show IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      priorCov hPrior.posSemidef)
    infer_instance
  have hNoiseG : IsGaussian noiseGauss := by
    show IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
      (posSemidef_sq_smul_one (n := n) ν))
    infer_instance
  -- Both Gaussian factors are zero-mean: ∫ x ∂μ = 0.
  have hObsZero : ∫ y, y ∂obsGauss = (0 : EuclideanSpace ℝ (Fin n)) :=
    integral_id_multivariateGaussian_zero (d := n) _ hObs
  have hPostZero : ∫ ε, ε ∂postGauss = (0 : EuclideanSpace ℝ (Fin d)) :=
    integral_id_multivariateGaussian_zero (d := d) _ hPost
  have hPriorZero : ∫ θ, θ ∂priorGauss = (0 : EuclideanSpace ℝ (Fin d)) :=
    integral_id_multivariateGaussian_zero (d := d) _ hPrior.posSemidef
  have hNoiseZero : ∫ y, y ∂noiseGauss = (0 : EuclideanSpace ℝ (Fin n)) :=
    integral_id_multivariateGaussian_zero (d := n) _ _
  -- Integrability of identity for the four Gaussian factors.
  have hObsInt : Integrable (id : EuclideanSpace ℝ (Fin n) → _) obsGauss :=
    ProbabilityTheory.IsGaussian.integrable_id (μ := obsGauss)
  have hPostInt : Integrable (id : EuclideanSpace ℝ (Fin d) → _) postGauss :=
    ProbabilityTheory.IsGaussian.integrable_id (μ := postGauss)
  have hPriorInt : Integrable (id : EuclideanSpace ℝ (Fin d) → _) priorGauss :=
    ProbabilityTheory.IsGaussian.integrable_id (μ := priorGauss)
  have hNoiseInt : Integrable (id : EuclideanSpace ℝ (Fin n) → _) noiseGauss :=
    ProbabilityTheory.IsGaussian.integrable_id (μ := noiseGauss)
  -- Helper: the integral of `id` against the product of the two
  -- LHS Gaussian factors is `(0, 0)`. Applies
  -- `MeasureTheory.integral_continuousLinearMap_prod` with
  -- `L = ContinuousLinearMap.id`. Each summand integrates a pair
  -- `(x, 0)` or `(0, y)`, which we compute via `fst_integral` /
  -- `snd_integral` applied to the joint integrability of the pair.
  have integral_prod_zero_LHS :
      ∫ p, p ∂(obsGauss.prod postGauss)
        = (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) := by
    have h := MeasureTheory.integral_continuousLinearMap_prod
      (μ := obsGauss) (ν := postGauss)
      (L := ContinuousLinearMap.id ℝ
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)))
      hObsInt hPostInt
    simp only [ContinuousLinearMap.id_apply] at h
    rw [h]
    -- Each summand: ∫ (x, 0) ∂μ = (∫ x, ∫ 0) = (0, 0).
    have hμsum : ∫ x, ((ContinuousLinearMap.id ℝ
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d))).comp
        (ContinuousLinearMap.inl ℝ
          (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin d)))) x ∂obsGauss
          = (0, 0) := by
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.inl_apply]
      refine Prod.ext ?_ ?_
      · rw [fst_integral (by exact hObsInt.prodMk (integrable_const _))]
        simpa using hObsZero
      · rw [snd_integral (by exact hObsInt.prodMk (integrable_const _))]
        simp
    have hνsum : ∫ y, ((ContinuousLinearMap.id ℝ
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d))).comp
        (ContinuousLinearMap.inr ℝ
          (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin d)))) y ∂postGauss
          = (0, 0) := by
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.inr_apply]
      refine Prod.ext ?_ ?_
      · rw [fst_integral (by exact (integrable_const _).prodMk hPostInt)]
        simp
      · rw [snd_integral (by exact (integrable_const _).prodMk hPostInt)]
        simpa using hPostZero
    rw [hμsum, hνsum]
    simp
  -- Same for RHS factors.
  have integral_prod_zero_RHS :
      ∫ p, p ∂(priorGauss.prod noiseGauss)
        = (0 : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) := by
    have h := MeasureTheory.integral_continuousLinearMap_prod
      (μ := priorGauss) (ν := noiseGauss)
      (L := ContinuousLinearMap.id ℝ
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
      hPriorInt hNoiseInt
    simp only [ContinuousLinearMap.id_apply] at h
    rw [h]
    have hμsum : ∫ x, ((ContinuousLinearMap.id ℝ
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))).comp
        (ContinuousLinearMap.inl ℝ
          (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)))) x ∂priorGauss
          = (0, 0) := by
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.inl_apply]
      refine Prod.ext ?_ ?_
      · rw [fst_integral (by exact hPriorInt.prodMk (integrable_const _))]
        simpa using hPriorZero
      · rw [snd_integral (by exact hPriorInt.prodMk (integrable_const _))]
        simp
    have hνsum : ∫ y, ((ContinuousLinearMap.id ℝ
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))).comp
        (ContinuousLinearMap.inr ℝ
          (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)))) y ∂noiseGauss
          = (0, 0) := by
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.inr_apply]
      refine Prod.ext ?_ ?_
      · rw [fst_integral (by exact (integrable_const _).prodMk hNoiseInt)]
        simp
      · rw [snd_integral (by exact (integrable_const _).prodMk hNoiseInt)]
        simpa using hNoiseZero
    rw [hμsum, hνsum]
    simp
  refine ⟨?_, ?_⟩
  · -- LHS branch.
    -- Rewrite `joint.snd = obsGauss`.
    have hSnd : (jointPriorObservation priorCov hPrior.posSemidef X ν).snd =
        obsGauss :=
      jointPriorObservation_snd_eq_multivariateGaussian
        priorCov hPrior.posSemidef X ν hObs
    rw [hSnd]
    -- Apply Sub-I4.A: compProd is map of independent product.
    rw [gaussianPosteriorKernel_compProd_eq_map_prod
        priorCov X ν hObs hPost]
    -- Apply `integral_id_map` for the CLM `posteriorJointMap`.
    have hProdInt : Integrable (id : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin d) → _) (obsGauss.prod postGauss) :=
      ProbabilityTheory.IsGaussian.integrable_id (μ := obsGauss.prod postGauss)
    rw [ContinuousLinearMap.integral_id_map hProdInt (posteriorJointMap priorCov X ν)]
    -- Now goal: posteriorJointMap (∫ p, p ∂(obsGauss.prod postGauss)) = 0.
    rw [integral_prod_zero_LHS]
    -- `posteriorJointMap 0 = 0` by linearity.
    exact map_zero (posteriorJointMap priorCov X ν)
  · -- RHS branch.
    -- Rewrite the joint as a pushforward.
    rw [jointPriorObservation_eq_map_prod priorCov hPrior.posSemidef X ν]
    -- Combine the two `.map`s.
    have hΨ : Measurable (observationJointMap X) :=
      (observationJointMap X).continuous.measurable
    rw [Measure.map_map (measurable_swap) hΨ]
    -- Express `Prod.swap ∘ observationJointMap X` as a single CLM
    -- composition. Define `swapCLM : E_d × E_n →L[ℝ] E_n × E_d` as the
    -- continuous linear equivalence `prodComm` coerced to a CLM.
    set swapCLM : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) :=
      (ContinuousLinearEquiv.prodComm ℝ
        (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n))).toContinuousLinearMap
      with hswapCLM
    -- The composition CLM has underlying function `Prod.swap ∘ observationJointMap X`.
    set totalCLM : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) :=
      swapCLM.comp (observationJointMap X) with htotalCLM
    have htotal_fun :
        (Prod.swap ∘ observationJointMap X) =
          (totalCLM : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →
            EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) := by
      funext p
      simp [totalCLM, swapCLM, ContinuousLinearEquiv.prodComm,
        observationJointMap_apply]
    rw [htotal_fun]
    -- Now apply `integral_id_map` with `totalCLM`.
    have hProdInt : Integrable (id : EuclideanSpace ℝ (Fin d) ×
        EuclideanSpace ℝ (Fin n) → _) (priorGauss.prod noiseGauss) :=
      ProbabilityTheory.IsGaussian.integrable_id (μ := priorGauss.prod noiseGauss)
    rw [ContinuousLinearMap.integral_id_map hProdInt totalCLM]
    -- Goal: totalCLM (∫ p, p ∂(priorGauss.prod noiseGauss)) = 0.
    rw [integral_prod_zero_RHS]
    exact map_zero totalCLM

end ProbabilityTheory
