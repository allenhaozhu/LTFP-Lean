/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Calculus.GradientFlowRandomInit
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Parameter-movement bound from a bounded trajectory derivative

A differentiable real-time curve in a normed space with `‖α'(t)‖ ≤ K`
satisfies `‖α(t) - α(t₀)‖ ≤ K · |t - t₀|`. Used downstream by B8 N5
for the parameter-movement step of lazy-training analysis.
-/

namespace LTFP.MathlibExt.Calculus

theorem parameter_movement_of_bounded_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ → E) (K : NNReal) (hα : Differentiable ℝ α)
    (hbound : ∀ t : ℝ, ‖deriv α t‖₊ ≤ K) (t t₀ : ℝ) :
    dist (α t) (α t₀) ≤ (K : ℝ) * |t - t₀| := by
  have hlip : LipschitzWith K α :=
    lipschitzWith_of_nnnorm_deriv_le (𝕜 := ℝ) (f := α) hα hbound
  simpa [Real.dist_eq] using hlip.dist_le_mul t t₀

/-- Norm-form variant of `parameter_movement_of_bounded_deriv` for use
in the lazy-training family: the conclusion `‖α t - α t₀‖ ≤ K · |t - t₀|`
restates the distance bound through `dist_eq_norm`. -/
theorem parameter_movement_of_bounded_deriv_norm_form
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ → E) (K : NNReal) (hα : Differentiable ℝ α)
    (hbound : ∀ t : ℝ, ‖deriv α t‖₊ ≤ K) (t t₀ : ℝ) :
    ‖α t - α t₀‖ ≤ (K : ℝ) * |t - t₀| := by
  simpa [dist_eq_norm] using
    parameter_movement_of_bounded_deriv α K hα hbound t t₀

end LTFP.MathlibExt.Calculus
