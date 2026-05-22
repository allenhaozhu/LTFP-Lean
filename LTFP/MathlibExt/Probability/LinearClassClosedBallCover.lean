/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Total boundedness and finite cover for parameter closed ball

Bridging round 19's `linear_class_covering_number_lt_top` (existence of
finite covering number) to the downstream-usable forms: total boundedness
and an explicit finite cover satisfying the parameter-cover predicate
used by `linear_class_sample_cover_of_param_cover` (round 17).
-/

theorem linear_class_closed_ball_totallyBounded
    {d : ℕ} (B : ℝ) :
    TotallyBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) B).totallyBounded

theorem linear_class_closed_ball_exists_finite_cover
    {d : ℕ} (B δ : ℝ) (hδ : 0 < δ) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin d)),
      ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ B →
        ∃ c ∈ C, ‖θ - c‖ ≤ δ := by
  classical
  have hTB : TotallyBounded
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B) :=
    linear_class_closed_ball_totallyBounded (d := d) B
  -- TotallyBounded gives a finite cover at every ε > 0 (metric form).
  rcases (Metric.totallyBounded_iff.mp hTB) δ hδ with ⟨C, hCfin, hCcov⟩
  refine ⟨hCfin.toFinset, fun θ hθ => ?_⟩
  have hθA : θ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hθ
  have hcover := hCcov hθA
  -- hcover : θ ∈ ⋃ y ∈ C, Metric.ball y δ
  rw [Set.mem_iUnion₂] at hcover
  rcases hcover with ⟨c, hcC, hdist⟩
  refine ⟨c, ?_, ?_⟩
  · simpa [Set.Finite.mem_toFinset] using hcC
  · have hlt : dist θ c < δ := hdist
    have hle : dist θ c ≤ δ := le_of_lt hlt
    simpa [dist_eq_norm] using hle
