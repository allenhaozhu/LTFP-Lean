/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianMeasure
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
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

/-- **Vector form of the Gaussian observation kernel mean.**
The integral of `y` against the observation kernel `N(X θ, ν² · I)`
equals `regressionCLM X θ` (i.e., `X θ` viewed as an element of
`EuclideanSpace ℝ (Fin n)`).

This aggregates the coordinate-wise identity
`gaussianObservationKernel_integral_eval` over all `i : Fin n`,
using `PiLp.ext` and `MeasureTheory.eval_integral_piLp` to reduce
vector equality to per-coordinate equality. Integrability of the
identity function against the kernel is supplied by Mathlib's
`IsGaussian.integrable_fun_id`, since the observation kernel is
Gaussian (`instIsGaussianGaussianObservationKernel`). -/
theorem gaussianObservationKernel_integral_vector
    {d n : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    ∫ y, y ∂(gaussianObservationKernel X ν θ) = regressionCLM X θ := by
  classical
  set μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    gaussianObservationKernel X ν θ with hμ
  -- `μ` is Gaussian, so the identity function is integrable, and so are
  -- all coordinates by `integrable_piLp_iff`.
  have hIntId : Integrable (fun y : EuclideanSpace ℝ (Fin n) => y) μ :=
    ProbabilityTheory.IsGaussian.integrable_fun_id (μ := μ)
  have hIntCoord : ∀ i, Integrable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (y : EuclideanSpace ℝ (Fin n)) i) μ := by
    intro i
    exact (MeasureTheory.integrable_piLp_iff (q := 2)
        (E := fun _ : Fin n => ℝ) (f := fun y => y)).mp hIntId i
  -- Reduce vector equality to coordinate-wise equality via `PiLp.ext`.
  refine PiLp.ext (fun i => ?_)
  rw [MeasureTheory.eval_integral_piLp (q := 2) (E := fun _ : Fin n => ℝ)
      (f := fun y : EuclideanSpace ℝ (Fin n) => y) hIntCoord i]
  -- Goal: `∫ y, y i ∂μ = (regressionCLM X θ) i`.
  -- `y i = (WithLp.ofLp y) i` definitionally, so the scalar lemma applies.
  show ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
          ∂(gaussianObservationKernel X ν θ)
        = (regressionCLM X θ) i
  -- And `(regressionCLM X θ) i = (WithLp.ofLp (regressionCLM X θ)) i`.
  exact gaussianObservationKernel_integral_eval X ν θ i
