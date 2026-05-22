/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianMeasure
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian observation kernel: coordinate mean

For the Gaussian observation kernel `Y | θ ~ N(X θ, ν² · I)`, the
coordinate-`i` integral of `y` against the kernel equals the
coordinate-`i` entry of the mean `X θ`. Bridge step inside B4 Node 2.
-/

open MeasureTheory ProbabilityTheory

theorem gaussianObservationKernel_integral_eval
    {d n : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
      ∂(gaussianObservationKernel X ν θ)
      = (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i := by
  rw [gaussianObservationKernel_apply]
  let μ0 := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
      (posSemidef_sq_smul_one (n := n) ν)
  have hmeas : Measurable (fun y : EuclideanSpace ℝ (Fin n) => regressionCLM X θ + y) := by
    fun_prop
  rw [integral_map hmeas.aemeasurable]
  · have hcoord_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) x) i) μ0 := by
      have hId : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x) μ0 := by
        simpa [μ0] using ProbabilityTheory.IsGaussian.integrable_fun_id (μ := μ0)
      simpa [PiLp.proj_apply] using
        (ContinuousLinearMap.integrable_comp
          (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin n => ℝ) i) hId)
    have hzero := integral_eval_multivariateGaussian
        (m := (0 : EuclideanSpace ℝ (Fin n)))
        (S := ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ)))
        (hS := posSemidef_sq_smul_one (n := n) ν) i
    have hconst_int : Integrable (fun _ : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i) μ0 :=
      integrable_const _
    calc
      ∫ x, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ + x)) i ∂μ0
          = ∫ x, ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i +
                (WithLp.ofLp (p := 2) (V := Fin n → ℝ) x) i) ∂μ0 := by
              refine integral_congr_ae (.of_forall ?_); intro x; simp
      _ = (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i +
            ∫ x, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) x) i ∂μ0 := by
              rw [integral_add hconst_int hcoord_int]; simp
      _ = (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i := by
              rw [hzero]; simp
  · fun_prop
