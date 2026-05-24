/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.LinearPredictorLipschitz
import LTFP.Ch02_SupervisedLearning.Defs

/-!
# Linearized squared-loss Lipschitz bound in the parameter

For a linear predictor `θ ↦ ⟨θ, x⟩` with bounded prediction error, the
squared loss `(⟨θ, x⟩ - y)²` is Lipschitz in `θ` on the ball `‖x‖ ≤ R`
with constant `2 B R`. Second intermediate toward B8 N6 (wide-network
generalization via N5).

The second theorem below restates the same Lipschitz inequality
directly for `LTFP.squareLoss` in terms of two close predictions `z`,
`z'` (rather than two parameter vectors `w`, `v`). This is B8 N6
Intermediate 2.
-/

open scoped RealInnerProductSpace

theorem linearized_risk_lipschitz_param
    {d : ℕ} (w v x : EuclideanSpace ℝ (Fin d)) (y B R : ℝ)
    (hx : ‖x‖ ≤ R)
    (hw : |inner ℝ w x - y| ≤ B)
    (hv : |inner ℝ v x - y| ≤ B) :
    |(inner ℝ w x - y) ^ 2 - (inner ℝ v x - y) ^ 2|
      ≤ (2 * B) * (‖w - v‖ * R) := by
  set a : ℝ := inner ℝ w x - y with ha_def
  set b : ℝ := inner ℝ v x - y with hb_def
  have hdiff : |a - b| ≤ ‖w - v‖ * R := by
    have hab : a - b = inner ℝ w x - inner ℝ v x := by
      show (inner ℝ w x - y) - (inner ℝ v x - y) = inner ℝ w x - inner ℝ v x
      ring
    rw [hab]
    exact linear_predictor_lipschitz_on_ball w v x R hx
  have hsum : |a + b| ≤ 2 * B := by
    calc |a + b|
        ≤ |a| + |b| := abs_add_le a b
      _ ≤ B + B := add_le_add hw hv
      _ = 2 * B := by ring
  have hR_nonneg : 0 ≤ ‖w - v‖ * R := by
    exact le_trans (abs_nonneg _) hdiff
  have hprod : |a - b| * |a + b| ≤ (‖w - v‖ * R) * (2 * B) := by
    exact mul_le_mul hdiff hsum (abs_nonneg _) hR_nonneg
  calc |a ^ 2 - b ^ 2|
      = |(a - b) * (a + b)| := by
          congr 1
          ring
    _ = |a - b| * |a + b| := abs_mul (a - b) (a + b)
    _ ≤ (‖w - v‖ * R) * (2 * B) := hprod
    _ = (2 * B) * (‖w - v‖ * R) := by ring

/-- B8 N6 Intermediate 2 — Lipschitz bound for the squared loss in the
prediction. If two predictions `z`, `z'` are both within `B` of the
label `y` and within `η` of each other, then their squared losses differ
by at most `2 B η`. This restates `linearized_risk_lipschitz_param`
without the linear-predictor structure: the Lipschitz constant depends
only on the prediction error bound `B` and the prediction gap `η`. -/
theorem squareLoss_sub_squareLoss_le_of_pred_close
    {z z' y B η : ℝ}
    (hz : |z - y| ≤ B) (hz' : |z' - y| ≤ B)
    (hclose : |z - z'| ≤ η) :
    |LTFP.squareLoss z y - LTFP.squareLoss z' y| ≤ 2 * B * η := by
  unfold LTFP.squareLoss
  set a : ℝ := z - y with ha_def
  set b : ℝ := z' - y with hb_def
  have hdiff : |a - b| ≤ η := by
    have hab : a - b = z - z' := by
      show (z - y) - (z' - y) = z - z'
      ring
    rw [hab]; exact hclose
  have hsum : |a + b| ≤ 2 * B := by
    calc |a + b|
        ≤ |a| + |b| := abs_add_le a b
      _ ≤ B + B := add_le_add hz hz'
      _ = 2 * B := by ring
  have hη_nonneg : 0 ≤ η := le_trans (abs_nonneg _) hdiff
  have hprod : |a - b| * |a + b| ≤ η * (2 * B) :=
    mul_le_mul hdiff hsum (abs_nonneg _) hη_nonneg
  calc |a ^ 2 - b ^ 2|
      = |(a - b) * (a + b)| := by
          congr 1
          ring
    _ = |a - b| * |a + b| := abs_mul (a - b) (a + b)
    _ ≤ η * (2 * B) := hprod
    _ = 2 * B * η := by ring
