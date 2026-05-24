/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.GaussianPosteriorCompProdCovarianceBilinWrapped

/-!
# Gaussian posterior compProd equals swapped joint (B4 N2 Sub-I4.D)

The Gaussian conjugate-prior identity: the composition-product of the
observation marginal Gaussian with the Gaussian posterior kernel equals
the swap of the joint prior–observation measure.

This combines:

* Sub-I4.B (mean equality: both have zero mean as vectors)
* Sub-I4.D wrapped (covariance equality after pushing through the
  WithLp 2 wrap CLM)
* `IsGaussian.ext` on the wrapped measures (WithLp 2 of the product
  carries an inner-product instance) plus injectivity of pushforward
  along a continuous linear equivalence (to pull back to the plain
  product).
-/

open MeasureTheory ProbabilityTheory WithLp
open scoped Matrix ENNReal

namespace ProbabilityTheory

/-- **B4 N2 Sub-I4.D.** The Gaussian-posterior composition-product on
`(observation, parameter)` equals the swap of the joint prior–observation
measure. Mathematically the Bayesian conjugate-prior identity. -/
theorem gaussianPosteriorKernel_compProd_eq_swapped_joint
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosDef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (hν : ν ≠ 0) :
    (jointPriorObservation priorCov hPrior.posSemidef X ν).snd ⊗ₘ
        gaussianPosteriorKernel priorCov X ν
          (gaussianPosterior_covariances_pos priorCov hPrior X ν hν).2
      = (jointPriorObservation priorCov hPrior.posSemidef X ν).map Prod.swap := by
  classical
  obtain ⟨hObsPD, hPost⟩ :=
    gaussianPosterior_covariances_pos priorCov hPrior X ν hν
  have hObs : (Matrix.obsCov priorCov X (ν ^ 2)).PosSemidef := hObsPD.posSemidef
  -- The two measures and the wrap CLM.
  set μL : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
    (jointPriorObservation priorCov hPrior.posSemidef X ν).snd ⊗ₘ
      gaussianPosteriorKernel priorCov X ν hPost with hμL_def
  set μR : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
    (jointPriorObservation priorCov hPrior.posSemidef X ν).map Prod.swap with hμR_def
  -- Gaussian instances on the underlying measures.
  have hμLGauss : IsGaussian μL := by
    show IsGaussian
      ((jointPriorObservation priorCov hPrior.posSemidef X ν).snd ⊗ₘ
        gaussianPosteriorKernel priorCov X ν hPost)
    rw [jointPriorObservation_snd_eq_multivariateGaussian
        priorCov hPrior.posSemidef X ν hObs]
    infer_instance
  have hμRGauss : IsGaussian μR := by
    show IsGaussian
      ((jointPriorObservation priorCov hPrior.posSemidef X ν).map Prod.swap)
    set swapCLM :
        EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) :=
      (ContinuousLinearEquiv.prodComm ℝ
        (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n))).toContinuousLinearMap
      with hswapCLM
    have hSwap_fun :
        (Prod.swap : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) =
          (swapCLM : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →
            EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) := by
      funext p; simp [swapCLM]
    rw [hSwap_fun]
    infer_instance
  -- The wrap continuous linear equivalence between the plain product
  -- and the WithLp 2 product. We use the equivalence form for invertibility.
  set wrapE :
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) ≃L[ℝ]
        WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin d))).symm with hwrapE_def
  set wrap : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) →L[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
    wrapEnEd n d with hwrap_def
  have hwrap_eq : (wrap :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) →
        WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d))) = wrapE := by
    rfl
  -- Gaussianity after wrapping.
  have hWrappedGauss_L : IsGaussian (μL.map wrap) := isGaussian_map (μ := μL) wrap
  have hWrappedGauss_R : IsGaussian (μR.map wrap) := isGaussian_map (μ := μR) wrap
  -- Means after wrapping coincide (both equal 0 in WithLp 2).
  have hMeanWrap : (μL.map wrap)[id] = (μR.map wrap)[id] := by
    have hMeanL : ∫ x, x ∂μL =
        (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
      (gaussianPosteriorKernel_compProd_integral_vector_eq_zero
        priorCov hPrior X ν hν).1
    have hMeanR : ∫ x, x ∂μR =
        (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
      (gaussianPosteriorKernel_compProd_integral_vector_eq_zero
        priorCov hPrior X ν hν).2
    -- Lift through wrap CLM: `(μ.map wrap)[id] = wrap (μ[id])` for CLM `wrap`.
    have hIntL : Integrable (id : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin d) → _) μL :=
      ProbabilityTheory.IsGaussian.integrable_id (μ := μL)
    have hIntR : Integrable (id : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin d) → _) μR :=
      ProbabilityTheory.IsGaussian.integrable_id (μ := μR)
    show ∫ x, x ∂(μL.map wrap) = ∫ x, x ∂(μR.map wrap)
    rw [ContinuousLinearMap.integral_id_map hIntL wrap,
      ContinuousLinearMap.integral_id_map hIntR wrap]
    rw [hMeanL, hMeanR]
  -- Covariance equality after wrapping (Sub-I4.D wrapped).
  have hCovWrap : covarianceBilin (μL.map wrap) = covarianceBilin (μR.map wrap) :=
    gaussianPosteriorKernel_compProd_covarianceBilin_wrapped_eq_swapped_joint
      priorCov hPrior X ν hν
  -- Apply `IsGaussian.ext` on the WithLp 2 side.
  have hWrappedEq : μL.map wrap = μR.map wrap :=
    IsGaussian.ext hMeanWrap hCovWrap
  -- Unwrap by pulling back through `wrapE.symm`.
  have hUnwrap : ∀ μ : Measure (EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin d)),
      (μ.map wrap).map (wrapE.symm : WithLp 2 (EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin d)) →L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) = μ := by
    intro μ
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    show μ.map ((wrapE.symm : WithLp 2 _ →L[ℝ] _) ∘ wrap) = μ
    have hcomp : (wrapE.symm : WithLp 2 _ →L[ℝ] _) ∘
        (wrap : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) →
          WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d))) = id := by
      funext p
      show wrapE.symm (wrap p) = p
      rw [hwrap_eq]
      exact wrapE.symm_apply_apply p
    rw [hcomp, Measure.map_id]
  show μL = μR
  rw [← hUnwrap μL, ← hUnwrap μR, hWrappedEq]

end ProbabilityTheory
