/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.JointPriorObservationSndMean
import LTFP.MathlibExt.Probability.Distributions.RegressionCLMCovariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Joint prior-observation cross-covariance per coord-pair

Sub-step toward the B4 N2 carrier: the cross-covariance entry
`∫ θ_a · y_b ∂joint = (priorCov · Xᵀ)_{a, b}`. Combines with the
mean-zero and snd-covariance identities to fully characterize the joint
prior-observation measure as a centered Gaussian with block covariance
`[[priorCov, priorCov · Xᵀ]; [X · priorCov, X · priorCov · Xᵀ + ν²·I]]`.

Proof outline:

1. Unfold `jointPriorObservation` to `prior ⊗ₘ κ` and apply
   `Measure.integral_compProd` to factor the joint integral as
   `∫ θ, ∫ y, θ_a · y_b ∂(κ θ) ∂prior`.
2. Pull the constant-in-`y` factor `θ_a` out of the inner integral via
   `integral_const_mul`, then use `gaussianObservationKernel_integral_eval`
   to compute `∫ y, y_b ∂(κ θ) = (regressionCLM X θ)_b`.
3. Expand `(regressionCLM X θ)_b = ∑ c, X b c · θ_c` via
   `ofLp_regressionCLM` and `Matrix.mulVec`/`dotProduct`.
4. Distribute the outer integral over the finite sum and pull the
   `X b c` constants out via `integral_finset_sum` + `integral_const_mul`.
5. Apply `covariance_multivariateGaussian` at mean 0 to compute each
   `∫ θ_a · θ_c ∂prior = priorCov a c`.
6. Identify the resulting `∑ c, X b c · priorCov a c` with
   `(priorCov * Xᵀ) a b` via `Matrix.mul_apply` and `Matrix.transpose_apply`.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace ProbabilityTheory

/-- **Cross-covariance entry of the joint prior-observation measure.**
For the joint Gaussian prior-observation measure
`jointPriorObservation priorCov hPrior X ν`, the integral of
`θ_a · y_b` against the joint equals `(priorCov · Xᵀ)_{a, b}`.

Combined with `jointPriorObservation_snd_covariance_eval`,
`jointPriorObservation_snd_integral_eval_coord`,
`jointPriorObservation_fst_integral_eval_coord`, and the per-coordinate
prior covariance, this fully characterizes the second-moment block
structure of the joint Gaussian measure. -/
theorem jointPriorObservation_cross_covariance_eval
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (a : Fin d) (b : Fin n) :
    ∫ p, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) p.1) a
       * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) b
       ∂(jointPriorObservation priorCov hPrior X ν)
      = (priorCov * Xᵀ) a b := by
  classical
  set prior : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior with hprior
  set κ : Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)) :=
    gaussianObservationKernel X ν with hκ
  -- Step 1: unfold the joint measure as `prior ⊗ₘ κ`.
  have hJoint :
      jointPriorObservation priorCov hPrior X ν = prior ⊗ₘ κ := rfl
  rw [hJoint]
  -- Step 2: integrability for `Measure.integral_compProd`.
  have hJointGauss : IsGaussian (prior ⊗ₘ κ) := by
    show IsGaussian (jointPriorObservation priorCov hPrior X ν)
    infer_instance
  have hMemLpId : MemLp (id : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) → _)
      2 (prior ⊗ₘ κ) :=
    ProbabilityTheory.IsGaussian.memLp_two_id (μ := prior ⊗ₘ κ)
  have hMemLpFst : MemLp (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)
      => p.1) 2 (prior ⊗ₘ κ) := by
    have hCLM := hMemLpId.continuousLinearMap_comp
      (ContinuousLinearMap.fst ℝ
        (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)))
    simpa using hCLM
  have hMemLpSnd : MemLp (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)
      => p.2) 2 (prior ⊗ₘ κ) := by
    have hCLM := hMemLpId.continuousLinearMap_comp
      (ContinuousLinearMap.snd ℝ
        (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)))
    simpa using hCLM
  have hMemLpFstCoord : ∀ k : Fin d,
      MemLp (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin d → ℝ) p.1) k) 2 (prior ⊗ₘ κ) := by
    intro k
    exact MemLp.eval_piLp hMemLpFst k
  have hMemLpSndCoord : ∀ k : Fin n,
      MemLp (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) k) 2 (prior ⊗ₘ κ) := by
    intro k
    exact MemLp.eval_piLp hMemLpSnd k
  have hIntegrable :
      Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin d → ℝ) p.1) a
          * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) b)
        (prior ⊗ₘ κ) := by
    have := MemLp.integrable_mul (hMemLpFstCoord a) (hMemLpSndCoord b)
    simpa [Pi.mul_apply] using this
  rw [MeasureTheory.Measure.integral_compProd hIntegrable]
  -- Goal: `∫ θ, ∫ y, (ofLp θ)_a · (ofLp y)_b ∂(κ θ) ∂prior = (priorCov · Xᵀ) a b`.
  -- Step 3: pull `(ofLp θ)_a` out of the inner integral and apply the
  -- kernel-mean lemma, then expand via `ofLp_regressionCLM`/`mulVec`.
  have hInner : ∀ θ : EuclideanSpace ℝ (Fin d),
      ∫ y, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a
         * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) b ∂(κ θ)
        = ∑ c, (X b c)
            * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a
                * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) c) := by
    intro θ
    rw [integral_const_mul]
    have hKernel :
        ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) b ∂(κ θ)
          = (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) b := by
      show ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) b
              ∂(gaussianObservationKernel X ν θ) = _
      exact gaussianObservationKernel_integral_eval X ν θ b
    rw [hKernel]
    -- Now: `(ofLp θ)_a * (ofLp (regressionCLM X θ))_b = ∑ c, X b c * ((ofLp θ)_a * (ofLp θ)_c)`.
    rw [ofLp_regressionCLM]
    have hb : (X *ᵥ WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b
                = ∑ c, X b c * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) c := by
      simp [Matrix.mulVec, dotProduct]
    rw [hb, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro c _
    ring
  simp_rw [hInner]
  -- Goal: `∫ θ, ∑ c, X b c * ((ofLp θ)_a * (ofLp θ)_c) ∂prior = (priorCov * Xᵀ) a b`.
  -- Step 4: integrability for prior-side products.
  have hMemLpIdPrior : MemLp (id : EuclideanSpace ℝ (Fin d) → _) 2 prior :=
    ProbabilityTheory.IsGaussian.memLp_two_id (μ := prior)
  have hMemLpThetaCoord : ∀ k : Fin d,
      MemLp (fun θ : EuclideanSpace ℝ (Fin d) =>
        (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) k) 2 prior := by
    intro k
    exact MemLp.eval_piLp hMemLpIdPrior k
  have hIntCoord : ∀ k l : Fin d,
      Integrable (fun θ : EuclideanSpace ℝ (Fin d) =>
        (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) k
          * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) l) prior := by
    intro k l
    have := MemLp.integrable_mul (hMemLpThetaCoord k) (hMemLpThetaCoord l)
    simpa [Pi.mul_apply] using this
  have hIntSummand : ∀ c ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun θ : EuclideanSpace ℝ (Fin d) =>
        (X b c) * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a
          * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) c)) prior := by
    intros c _
    exact (hIntCoord a c).const_mul _
  -- Step 5: per-coordinate covariance of the prior.
  have hCoord : ∀ k l : Fin d,
      ∫ θ, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) k
         * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) l ∂prior
        = priorCov k l := by
    intro k l
    have h := covariance_multivariateGaussian
      (m := (0 : EuclideanSpace ℝ (Fin d))) (S := priorCov) (hS := hPrior) k l
    simpa [hprior] using h
  -- Distribute the integral over the finite sum, pull the X b c constants.
  rw [integral_finset_sum (Finset.univ : Finset (Fin d)) hIntSummand]
  -- Goal: `∑ c, ∫ θ, X b c * (θ_a * θ_c) ∂prior = (priorCov * Xᵀ) a b`.
  have hLHS :
      ∑ c, ∫ θ, (X b c) * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a
              * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) c) ∂prior
        = ∑ c, (X b c) * priorCov a c := by
    refine Finset.sum_congr rfl ?_
    intros c _
    rw [integral_const_mul]
    rw [hCoord a c]
  rw [hLHS]
  -- Step 6: identify `∑ c, X b c * priorCov a c` with `(priorCov * Xᵀ) a b`.
  -- `(priorCov * Xᵀ) a b = ∑ c, priorCov a c * Xᵀ c b = ∑ c, priorCov a c * X b c`.
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl ?_
  intros c _
  ring

end ProbabilityTheory
