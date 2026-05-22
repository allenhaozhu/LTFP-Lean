/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Finite covering number of a closed parameter ball

For the closed ball `‖θ‖ ≤ B` in `EuclideanSpace ℝ (Fin d)`, the
`δ`-covering number is finite for any `δ > 0`. Sub-step toward the
classical `(3B/δ)^d` bound (which is the explicit cardinality version
this gives only existence-of-finite-cover).
-/

open scoped NNReal

theorem linear_class_covering_number_lt_top
    {d : ℕ} (B δ : ℝ≥0) (hδ : δ ≠ 0) :
    Metric.coveringNumber δ
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (B : ℝ)) < ⊤ := by
  classical
  let A := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (B : ℝ)
  rcases Metric.exists_finite_isCover_of_isCompact (s := A) hδ
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) (B : ℝ)) with
    ⟨C, hCsub, hCfin, hCcov⟩
  exact (Metric.IsCover.coveringNumber_le_encard hCsub hCcov).trans_lt hCfin.encard_lt_top
