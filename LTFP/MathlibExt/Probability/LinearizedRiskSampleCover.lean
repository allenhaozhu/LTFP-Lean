/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.LinearizedRiskLipschitz
import LTFP.MathlibExt.Probability.LinearClassSampleCover

/-!
# Sample cover for the linearized squared-loss class

Composes `linearized_risk_lipschitz_param` with the parameter-cover
hypothesis: a parameter `δ`-cover of `Θ` yields a `(2 B δ R)`-cover of
the squared-loss values on any bounded sample, when the prediction
error is uniformly bounded by `B`. Bridge step on the B8 N6 path.
-/

open scoped RealInnerProductSpace

theorem linearized_risk_class_sample_cover_of_param_cover
    {d m : ℕ} (Θ C : Set (EuclideanSpace ℝ (Fin d)))
    (xs : Fin m → EuclideanSpace ℝ (Fin d))
    (ys : Fin m → ℝ)
    (δ R B : ℝ)
    (hx : ∀ i : Fin m, ‖xs i‖ ≤ R)
    (hcover : ∀ θ ∈ Θ, ∃ c ∈ C, ‖θ - c‖ ≤ δ)
    (hbound : ∀ θ ∈ Θ, ∀ i : Fin m, |inner ℝ θ (xs i) - ys i| ≤ B)
    (hboundC : ∀ c ∈ C, ∀ i : Fin m, |inner ℝ c (xs i) - ys i| ≤ B) :
    ∀ θ ∈ Θ, ∃ c ∈ C,
      ∀ i : Fin m,
        |(inner ℝ θ (xs i) - ys i) ^ 2 - (inner ℝ c (xs i) - ys i) ^ 2|
          ≤ (2 * B) * (δ * R) := by
  intro θ hθ
  rcases hcover θ hθ with ⟨c, hc, hδ⟩
  refine ⟨c, hc, fun i => ?_⟩
  have hw := hbound θ hθ i
  have hv := hboundC c hc i
  have hstep :
      |(inner ℝ θ (xs i) - ys i) ^ 2 - (inner ℝ c (xs i) - ys i) ^ 2|
        ≤ (2 * B) * (‖θ - c‖ * R) :=
    linearized_risk_lipschitz_param θ c (xs i) (ys i) B R (hx i) hw hv
  have hB_nonneg : 0 ≤ 2 * B := by
    have hBpos : 0 ≤ B := le_trans (abs_nonneg _) hw
    linarith
  have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg _) (hx i)
  have hmono : (2 * B) * (‖θ - c‖ * R) ≤ (2 * B) * (δ * R) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hδ hR_nonneg) hB_nonneg
  exact hstep.trans hmono
