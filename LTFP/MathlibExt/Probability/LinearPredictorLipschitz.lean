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
