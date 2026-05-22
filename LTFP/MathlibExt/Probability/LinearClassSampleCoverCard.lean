/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Finset.Card
import LTFP.MathlibExt.Probability.LinearPredictorLipschitz

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

/-- Covering of the sample-prediction set: a finite parameter `δ`-cover
of `Θ` gives a sample-prediction set of size at most `|C|` whose elements
approximate every `θ ∈ Θ`'s sample-prediction tuple to within `δ · R` in
the entrywise (`L∞` on the sample) sense, where `R` is a uniform norm
bound on the sample. Composition of `Finset.card_image_le` with the
sample-wise linear-predictor Lipschitz bound. -/
theorem linear_class_sample_pred_covering_size_le
    {d m : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (C : Finset (EuclideanSpace ℝ (Fin d)))
    (xs : Fin m → EuclideanSpace ℝ (Fin d)) (δ R : ℝ)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hcover : ∀ θ ∈ Θ, ∃ c ∈ C, ‖θ - c‖ ≤ δ) :
    let predSet := (C.image (fun c => fun i : Fin m => inner ℝ c (xs i)))
    predSet.card ≤ C.card ∧
    ∀ θ ∈ Θ, ∃ p ∈ predSet,
      ∀ i : Fin m, |inner ℝ θ (xs i) - p i| ≤ δ * R := by
  refine ⟨Finset.card_image_le, fun θ hθ => ?_⟩
  rcases hcover θ hθ with ⟨c, hc, hδ⟩
  refine ⟨(fun i : Fin m => inner ℝ c (xs i)),
    Finset.mem_image.mpr ⟨c, hc, rfl⟩, fun i => ?_⟩
  have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg _) (hx i)
  have hlip := linear_predictor_lipschitz_on_ball θ c (xs i) R (hx i)
  exact hlip.trans (mul_le_mul_of_nonneg_right hδ hR_nonneg)
