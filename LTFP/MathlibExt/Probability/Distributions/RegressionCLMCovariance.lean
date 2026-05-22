/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianMeasure
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Cross-covariance of `regressionCLM` under the prior

For the design matrix `X` and a centered Gaussian prior with covariance
`priorCov`, the cross-integral of two coordinates of `regressionCLM X θ`
equals the corresponding entry of `X * priorCov * Xᵀ`. Sub-step toward
the full `joint.snd` covariance for the B4 N2 carrier.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace ProbabilityTheory

theorem regressionCLM_covariance_under_prior
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (i j : Fin n) :
    ∫ θ, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i
       * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) j
       ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior)
      = (X * priorCov * Xᵀ) i j := by
  classical
  set prior : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior with hprior
  -- Step A: per-coordinate covariance of the prior.
  -- `covariance_multivariateGaussian` at `m = 0` gives
  -- `∫ (ofLp θ) a * (ofLp θ) b ∂prior = priorCov a b`.
  have hCoord : ∀ a b : Fin d,
      ∫ θ, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a
         * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b ∂prior
        = priorCov a b := by
    intro a b
    have h := covariance_multivariateGaussian
      (m := (0 : EuclideanSpace ℝ (Fin d))) (S := priorCov) (hS := hPrior) a b
    simpa [hprior] using h
  -- Step B: integrability of `(ofLp θ) a * (ofLp θ) b` against the Gaussian prior.
  -- Each coordinate sits in `MemLp 2 prior` (Gaussian moments), and the product of
  -- two `MemLp 2` functions is in `MemLp 1 = Integrable` by Hölder with 1/2+1/2=1.
  have hPriorG : IsGaussian prior := by
    show IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior)
    infer_instance
  have hMemLpId : MemLp (id : EuclideanSpace ℝ (Fin d) → _) 2 prior :=
    ProbabilityTheory.IsGaussian.memLp_two_id (μ := prior)
  have hMemLpCoord : ∀ a : Fin d,
      MemLp (fun θ : EuclideanSpace ℝ (Fin d) =>
        (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a) 2 prior := by
    intro a
    exact MemLp.eval_piLp hMemLpId a
  have hIntCoord : ∀ a b : Fin d,
      Integrable (fun θ : EuclideanSpace ℝ (Fin d) =>
        (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a
          * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b) prior := by
    intro a b
    have := MemLp.integrable_mul (hMemLpCoord a) (hMemLpCoord b)
    simpa [Pi.mul_apply] using this
  -- Step C: expand each integrand coordinate via `ofLp_regressionCLM` and `mulVec`.
  have hExpand : ∀ θ : EuclideanSpace ℝ (Fin d),
      (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i
        * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) j
        = ∑ a, ∑ b, (X i a * X j b)
            * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a
                * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b) := by
    intro θ
    rw [ofLp_regressionCLM]
    have hi : (X *ᵥ WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) i
                = ∑ a, X i a * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a := by
      simp [Matrix.mulVec, dotProduct]
    have hj : (X *ᵥ WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) j
                = ∑ b, X j b * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b := by
      simp [Matrix.mulVec, dotProduct]
    rw [hi, hj, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    ring
  -- Step D: push the integral through the (finite) double sum and pull constants out.
  have hIntInner : ∀ a, ∀ b ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun θ : EuclideanSpace ℝ (Fin d) =>
        (X i a * X j b)
          * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a
              * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b)) prior := by
    intros a b _
    exact (hIntCoord a b).const_mul _
  have hIntOuter : ∀ a ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun θ : EuclideanSpace ℝ (Fin d) =>
        ∑ b, (X i a * X j b)
          * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a
              * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b)) prior := by
    intros a _
    exact integrable_finset_sum (Finset.univ : Finset (Fin d)) (hIntInner a)
  -- Compute the LHS in terms of `priorCov`.
  have hLHS :
      ∫ θ, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i
         * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) j ∂prior
        = ∑ a, ∑ b, (X i a * X j b) * priorCov a b := by
    simp_rw [hExpand]
    rw [integral_finset_sum (Finset.univ : Finset (Fin d)) hIntOuter]
    refine Finset.sum_congr rfl ?_
    intros a _
    rw [integral_finset_sum (Finset.univ : Finset (Fin d)) (hIntInner a)]
    refine Finset.sum_congr rfl ?_
    intros b _
    rw [integral_const_mul]
    rw [hCoord a b]
  -- Step E: expand the RHS.
  have hRHS : (X * priorCov * Xᵀ) i j
      = ∑ a, ∑ b, (X i a * X j b) * priorCov a b := by
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intros a _
    refine Finset.sum_congr rfl ?_
    intros b _
    ring
  rw [hLHS, hRHS]

end ProbabilityTheory
