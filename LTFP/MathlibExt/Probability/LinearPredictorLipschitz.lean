/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Linear predictor Lipschitz constant

For a linear predictor `θ ↦ ⟨θ, x⟩`, the Lipschitz constant in `θ`
is `‖x‖`. First intermediate step toward B8 N6 (wide network
generalization).
-/

open scoped RealInnerProductSpace

theorem linear_predictor_lipschitz_param
    {d : ℕ} (w v x : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ w x - inner ℝ v x| ≤ ‖w - v‖ * ‖x‖ := by
  simpa [inner_sub_left] using abs_real_inner_le_norm (w - v) x

/-- Linear predictors over a bounded ball of inputs are uniformly Lipschitz in
the parameter, with Lipschitz constant equal to the ball radius. -/
theorem linear_predictor_lipschitz_on_ball
    {d : ℕ} (w v x : EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (hx : ‖x‖ ≤ R) :
    |inner ℝ w x - inner ℝ v x| ≤ ‖w - v‖ * R := by
  calc |inner ℝ w x - inner ℝ v x|
      ≤ ‖w - v‖ * ‖x‖ := linear_predictor_lipschitz_param w v x
    _ ≤ ‖w - v‖ * R := by
        exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
