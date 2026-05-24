/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.GaussianConjugatePosteriorSchur
import LTFP.MathlibExt.Probability.Distributions.JointPriorObservationSndMean

/-!
# Gaussian posterior kernel

The conditional kernel `θ | y` for the Gaussian conjugate-prior setup,
constructed explicitly as a Gaussian with affine mean `priorCov · Xᵀ · obsCov⁻¹ · y`
and covariance the Schur posterior covariance. Sub-step toward the B4 N2
carrier closure (gaussianPosteriorMean_ridge_form).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

noncomputable def gaussianPosteriorKernel
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (hPost : (Matrix.schurPosteriorCov priorCov X (ν ^ 2)).PosSemidef) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin d)) :=
  Kernel.map
    ((Kernel.deterministic (id : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n)) measurable_id)
      ×ₖ
      (Kernel.const (EuclideanSpace ℝ (Fin n))
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost)))
    (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) =>
      regressionCLM
        (priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹) p.1 + p.2)

theorem gaussianPosteriorKernel_apply
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (hPost : (Matrix.schurPosteriorCov priorCov X (ν ^ 2)).PosSemidef)
    (y : EuclideanSpace ℝ (Fin n)) :
    gaussianPosteriorKernel priorCov X ν hPost y =
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
        (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost).map
        (fun θ => regressionCLM
          (priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹) y + θ) := by
  classical
  unfold gaussianPosteriorKernel
  have hf : Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) =>
        regressionCLM
          (priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹) p.1 + p.2) := by
    refine Measurable.add ?_ measurable_snd
    exact (measurable_regressionCLM _).comp measurable_fst
  rw [Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.const_apply, MeasureTheory.Measure.dirac_prod]
  rw [Measure.map_map hf (by fun_prop : Measurable (Prod.mk (id y)))]
  rfl

theorem gaussianPosteriorKernel_integral_vector
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (hPost : (Matrix.schurPosteriorCov priorCov X (ν ^ 2)).PosSemidef)
    (y : EuclideanSpace ℝ (Fin n)) :
    ∫ θ, θ ∂(gaussianPosteriorKernel priorCov X ν hPost y) =
      regressionCLM
        (priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹) y := by
  rw [gaussianPosteriorKernel_apply]
  let μ0 := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost
  let m := regressionCLM
      (priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹) y
  have hmeas : Measurable (fun θ : EuclideanSpace ℝ (Fin d) => m + θ) := by
    fun_prop
  rw [integral_map hmeas.aemeasurable]
  · have hId : Integrable (fun θ : EuclideanSpace ℝ (Fin d) => θ) μ0 := by
      simpa [μ0] using ProbabilityTheory.IsGaussian.integrable_fun_id (μ := μ0)
    have hConst : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => m) μ0 :=
      integrable_const _
    calc
      ∫ θ, m + θ ∂μ0 =
          ∫ θ, (fun _ : EuclideanSpace ℝ (Fin d) => m) θ + θ ∂μ0 := rfl
      _ = (∫ _θ, m ∂μ0) + ∫ θ, θ ∂μ0 := integral_add hConst hId
      _ = m + 0 := by
        rw [integral_const, integral_id_multivariateGaussian_zero
          (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost]
        simp [μ0]
      _ = regressionCLM
          (priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹) y := by
        simp [m]
  · fun_prop
