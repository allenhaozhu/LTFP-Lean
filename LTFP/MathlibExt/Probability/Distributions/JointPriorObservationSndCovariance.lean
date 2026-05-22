/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.JointPriorObservationSnd
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianNoiseCovariance
import LTFP.MathlibExt.Probability.Distributions.RegressionCLMCovariance
import LTFP.MathlibExt.Probability.Distributions.GaussianObservationKernelMean
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Per-coordinate covariance of the joint prior-observation second marginal

For the joint Gaussian prior-observation measure
`jointPriorObservation priorCov hPrior X ν` (defined in
`MultivariateGaussianMeasure.lean`), the integral of `y_i · y_j` against
the second marginal equals `(X · priorCov · Xᵀ)_{i,j} + (ν² · I)_{i,j}`.

This is the B4 N2 carrier-progress milestone toward the Gaussian
conjugate-prior posterior covariance identity. Proof strategy:

1. Rewrite the second marginal as `gaussianObservationKernel X ν ∘ₘ prior`
   via `jointPriorObservation_snd`.
2. Convert to integration against `prior ⊗ₘ κ` composed with `snd`, then
   apply `Measure.integral_compProd` to factor as
   `∫ θ, ∫ y, y_i · y_j ∂(κ θ) ∂prior`.
3. Apply `gaussianObservationKernel_second_moment_eval` on the inner
   integral.
4. Distribute the outer integral over the two-term sum, getting
   `regressionCLM_covariance_under_prior` for the first term and a
   constant for the second.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace ProbabilityTheory

/-- **Per-coordinate covariance of the joint prior-observation second
marginal.**
For the joint Gaussian prior-observation measure
`jointPriorObservation priorCov hPrior X ν`, the integral of
`y_i · y_j` against the second marginal equals
`(X · priorCov · Xᵀ)_{i,j} + (ν² · I)_{i,j}`.

This carries the B4 N2 carrier-progress milestone: the unconditional
covariance of the observation `Y` decomposes as the model-induced
covariance `X · priorCov · Xᵀ` plus the isotropic noise covariance
`ν² · I`. -/
theorem jointPriorObservation_snd_covariance_eval
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (i j : Fin n) :
    ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
       * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
       ∂(jointPriorObservation priorCov hPrior X ν).snd
      = (X * priorCov * Xᵀ) i j
        + (ν ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) i j := by
  classical
  set prior : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior with hprior
  set κ : Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)) :=
    gaussianObservationKernel X ν with hκ
  -- Step 1: rewrite the second marginal.
  have hSnd :
      (jointPriorObservation priorCov hPrior X ν).snd = κ ∘ₘ prior := by
    show (jointPriorObservation priorCov hPrior X ν).snd =
      gaussianObservationKernel X ν ∘ₘ
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior
    exact jointPriorObservation_snd priorCov hPrior X ν
  rw [hSnd]
  -- Step 2: express the integral over `κ ∘ₘ prior` as integral over `prior ⊗ₘ κ`
  -- composed with `snd`.
  have hSndCompProd : κ ∘ₘ prior = (prior ⊗ₘ κ).snd :=
    (Measure.snd_compProd prior κ).symm
  rw [hSndCompProd]
  rw [Measure.snd]
  -- Cast through `integral_map`.
  rw [MeasureTheory.integral_map measurable_snd.aemeasurable
      (by fun_prop : AEStronglyMeasurable
        (fun y : EuclideanSpace ℝ (Fin n) =>
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
            * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j)
        ((prior ⊗ₘ κ).map Prod.snd))]
  -- Goal: `∫ p, (ofLp p.2) i * (ofLp p.2) j ∂(prior ⊗ₘ κ) =
  --       (X * priorCov * Xᵀ) i j + (ν^2 • 1) i j`.
  -- Step 3: factor through `integral_compProd`. Need integrability of
  -- `p ↦ (ofLp p.2) i * (ofLp p.2) j` against `prior ⊗ₘ κ`.
  have hJointGauss : IsGaussian (prior ⊗ₘ κ) := by
    show IsGaussian (jointPriorObservation priorCov hPrior X ν)
    infer_instance
  -- L² of the identity on the joint measure.
  have hMemLpId : MemLp (id : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) → _)
      2 (prior ⊗ₘ κ) :=
    ProbabilityTheory.IsGaussian.memLp_two_id (μ := prior ⊗ₘ κ)
  -- L² of `p.2`: apply the continuous linear `Prod.snd` clm.
  have hMemLpSnd : MemLp (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)
      => p.2) 2 (prior ⊗ₘ κ) := by
    have hCLM := hMemLpId.continuousLinearMap_comp
      (ContinuousLinearMap.snd ℝ
        (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)))
    simpa using hCLM
  -- L² of each coordinate of `p.2`.
  have hMemLpCoord : ∀ k : Fin n,
      MemLp (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) k) 2 (prior ⊗ₘ κ) := by
    intro k
    exact MemLp.eval_piLp hMemLpSnd k
  -- Integrability of the product `(ofLp p.2)_i * (ofLp p.2)_j`.
  have hIntegrable :
      Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) i
          * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) j)
        (prior ⊗ₘ κ) := by
    have := MemLp.integrable_mul (hMemLpCoord i) (hMemLpCoord j)
    simpa [Pi.mul_apply] using this
  rw [MeasureTheory.Measure.integral_compProd hIntegrable]
  -- Goal: `∫ θ, ∫ y, (ofLp y) i * (ofLp y) j ∂(κ θ) ∂prior =
  --       (X * priorCov * Xᵀ) i j + (ν^2 • 1) i j`.
  -- Step 4: apply gaussianObservationKernel_second_moment_eval.
  have hInner : ∀ θ : EuclideanSpace ℝ (Fin d),
      ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
         * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j ∂(κ θ)
        = (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i
          * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) j
          + (ν ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) i j := by
    intro θ
    show ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
            * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
            ∂(gaussianObservationKernel X ν θ) = _
    exact gaussianObservationKernel_second_moment_eval X ν θ i j
  simp_rw [hInner]
  -- Goal: `∫ θ, (ofLp (regressionCLM X θ)) i * (ofLp (regressionCLM X θ)) j
  --              + (ν^2 • 1) i j ∂prior =
  --       (X * priorCov * Xᵀ) i j + (ν^2 • 1) i j`.
  -- Step 5: distribute the outer integral over the sum, then apply
  -- `regressionCLM_covariance_under_prior` and `integral_const`.
  have hPriorG : IsGaussian prior := by
    show IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior)
    infer_instance
  have hPriorP : IsProbabilityMeasure prior := by
    show IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      priorCov hPrior)
    infer_instance
  -- Integrability of `(ofLp regressionCLM)_i * (ofLp regressionCLM)_j` against prior.
  have hMemLpIdPrior : MemLp (id : EuclideanSpace ℝ (Fin d) → _) 2 prior :=
    ProbabilityTheory.IsGaussian.memLp_two_id (μ := prior)
  have hMemLpThetaCoord : ∀ a : Fin d,
      MemLp (fun θ : EuclideanSpace ℝ (Fin d) =>
        (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a) 2 prior := by
    intro a; exact MemLp.eval_piLp hMemLpIdPrior a
  -- Apply continuous linear `regressionCLM X` to get L² of regression mean.
  have hMemLpReg : MemLp (fun θ : EuclideanSpace ℝ (Fin d) =>
      regressionCLM X θ) 2 prior := by
    have := hMemLpIdPrior.continuousLinearMap_comp (regressionCLM X)
    simpa using this
  have hMemLpRegCoord : ∀ k : Fin n,
      MemLp (fun θ : EuclideanSpace ℝ (Fin d) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) k) 2 prior := by
    intro k; exact MemLp.eval_piLp hMemLpReg k
  have hIntReg : Integrable
      (fun θ : EuclideanSpace ℝ (Fin d) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i
          * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) j) prior := by
    have := MemLp.integrable_mul (hMemLpRegCoord i) (hMemLpRegCoord j)
    simpa [Pi.mul_apply] using this
  have hIntConst : Integrable
      (fun _ : EuclideanSpace ℝ (Fin d) =>
        (ν ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) i j) prior :=
    integrable_const _
  rw [integral_add hIntReg hIntConst]
  -- Now: `∫ θ, μ_i * μ_j ∂prior + ∫ θ, (ν^2 • 1) i j ∂prior =
  --       (X * priorCov * Xᵀ) i j + (ν^2 • 1) i j`.
  have hReg :
      ∫ θ, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i
         * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) j ∂prior
        = (X * priorCov * Xᵀ) i j := by
    show ∫ θ, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i
         * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) j
       ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior)
      = (X * priorCov * Xᵀ) i j
    exact regressionCLM_covariance_under_prior priorCov hPrior X i j
  rw [hReg]
  -- Goal: `(X * priorCov * Xᵀ) i j + ∫ _, (ν^2 • 1) i j ∂prior =
  --       (X * priorCov * Xᵀ) i j + (ν^2 • 1) i j`.
  rw [integral_const, probReal_univ]
  simp

end ProbabilityTheory
