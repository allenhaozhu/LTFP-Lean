/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Calculus.ParameterMovementBoundedDeriv

/-!
# Function movement along a bounded-derivative parameter trajectory

If a parameter curve `α : ℝ → E` has bounded derivative `‖α'‖ ≤ K` and
a function `f : E → ℝ` is `L`-Lipschitz, then
`|f(α t) - f(α t₀)| ≤ L · K · |t - t₀|`. Composition of
`parameter_movement_of_bounded_deriv` with `LipschitzWith.dist_le_mul`.
Used downstream by B8 N5 (lazy training).
-/

namespace LTFP.MathlibExt.Calculus

theorem function_movement_of_lipschitz_along_bounded_curve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ → E) (K : NNReal) (hα : Differentiable ℝ α)
    (hbound : ∀ t : ℝ, ‖deriv α t‖₊ ≤ K)
    (f : E → ℝ) (L : NNReal) (hf : LipschitzWith L f)
    (t t₀ : ℝ) :
    |f (α t) - f (α t₀)| ≤ (L : ℝ) * (K : ℝ) * |t - t₀| := by
  have hmove : dist (α t) (α t₀) ≤ (K : ℝ) * |t - t₀| :=
    parameter_movement_of_bounded_deriv α K hα hbound t t₀
  have hf_dist : dist (f (α t)) (f (α t₀)) ≤ (L : ℝ) * dist (α t) (α t₀) := by
    have := hf.dist_le_mul (α t) (α t₀)
    simpa using this
  have hL_nonneg : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hchain : dist (f (α t)) (f (α t₀)) ≤ (L : ℝ) * ((K : ℝ) * |t - t₀|) :=
    hf_dist.trans (mul_le_mul_of_nonneg_left hmove hL_nonneg)
  simpa [Real.dist_eq, mul_assoc] using hchain

end LTFP.MathlibExt.Calculus
