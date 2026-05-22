/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Finset.Card

/-!
# Cardinality bound on sample predictions from a finite parameter cover

For a finite parameter cover `C` and a sample `xs`, the number of
distinct prediction-tuples induced by mapping each `c ∈ C` to
`(fun i => ⟨c, xs i⟩)` is at most `C.card`. Bridge step toward
covering-number bounds on the B8 N6 path.
-/

open scoped RealInnerProductSpace

/-- Cardinality of the induced prediction-tuple image is bounded by the
parameter cover cardinality. -/
theorem linear_class_sample_pred_card_le
    {d m : ℕ} (C : Finset (EuclideanSpace ℝ (Fin d)))
    (xs : Fin m → EuclideanSpace ℝ (Fin d)) :
    (C.image (fun c => fun i : Fin m => inner ℝ c (xs i))).card ≤ C.card :=
  Finset.card_image_le
