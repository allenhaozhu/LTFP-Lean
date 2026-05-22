/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.LinearPredictorLipschitz

/-!
# Linear class cover transfer

If `C` is a `δ`-cover of a parameter set `Θ` under the parameter norm,
then on any sample `xs : Fin m → EuclideanSpace ℝ (Fin d)` of inputs
bounded by `R`, `C` induces a `(δ · R)`-cover of the linear predictor
class restricted to the sample. Bridge step toward B8 N6.
-/

open scoped RealInnerProductSpace

theorem linear_class_sample_cover_of_param_cover
    {d m : ℕ} (Θ C : Set (EuclideanSpace ℝ (Fin d)))
    (xs : Fin m → EuclideanSpace ℝ (Fin d)) (δ R : ℝ)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hcover : ∀ θ ∈ Θ, ∃ c ∈ C, ‖θ - c‖ ≤ δ) :
    ∀ θ ∈ Θ, ∃ c ∈ C,
      ∀ i : Fin m, |inner ℝ θ (xs i) - inner ℝ c (xs i)| ≤ δ * R := by
  intro θ hθ
  rcases hcover θ hθ with ⟨c, hc, hδ⟩
  refine ⟨c, hc, fun i => ?_⟩
  calc |inner ℝ θ (xs i) - inner ℝ c (xs i)|
      ≤ ‖θ - c‖ * R := linear_predictor_lipschitz_on_ball θ c (xs i) R (hx i)
    _ ≤ δ * R :=
        mul_le_mul_of_nonneg_right hδ (le_trans (norm_nonneg _) (hx i))
