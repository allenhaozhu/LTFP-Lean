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

end ProbabilityTheory
