/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianMeasure
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Noise covariance coordinate identity

For the isotropic noise component `multivariateGaussian 0 (ν² · I) _`, the
coordinate-`(i,j)` covariance equals `(ν² · I)_{i,j}`. Sub-step toward
the B4 N2 carrier (full `joint.snd` covariance).
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

theorem covariance_noise_multivariateGaussian
    {n : ℕ} (ν : ℝ) (i j : Fin n) :
    ∫ y, ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
           - (WithLp.ofLp (p := 2) (V := Fin n → ℝ)
              (0 : EuclideanSpace ℝ (Fin n))) i)
         * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
           - (WithLp.ofLp (p := 2) (V := Fin n → ℝ)
              (0 : EuclideanSpace ℝ (Fin n))) j)
       ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (ν ^ 2 • 1)
          (posSemidef_sq_smul_one (n := n) ν))
      = (ν ^ 2 • 1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simpa using
    (covariance_multivariateGaussian
      (m := (0 : EuclideanSpace ℝ (Fin n)))
      (S := (ν ^ 2 • 1 : Matrix (Fin n) (Fin n) ℝ))
      (hS := posSemidef_sq_smul_one (n := n) ν) i j)

theorem gaussianObservationKernel_covariance_eval
    {d n : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (i j : Fin n) :
    ∫ y, ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i -
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i)
       * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j -
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) j)
       ∂(gaussianObservationKernel X ν θ)
      = (ν ^ 2 • 1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  rw [gaussianObservationKernel_apply]
  let μ0 := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
      (posSemidef_sq_smul_one (n := n) ν)
  have hmeas : Measurable (fun y : EuclideanSpace ℝ (Fin n) => regressionCLM X θ + y) := by
    fun_prop
  rw [integral_map hmeas.aemeasurable]
  · simpa [μ0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      covariance_noise_multivariateGaussian (n := n) ν i j
  · fun_prop

end ProbabilityTheory
