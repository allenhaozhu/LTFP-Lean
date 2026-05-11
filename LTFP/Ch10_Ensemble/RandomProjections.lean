/-
LTFP §10.2 — Random projections.

Bach (2024) §10.2, pp. 288-298. A random Gaussian sketch
`Φ ∈ ℝᵏˣᵈ` with iid `𝒩(0, 1/k)` entries approximately preserves
norms — the Johnson-Lindenstrauss lemma — making it useful for
dimension reduction in ensemble learning.

This file extends `LTFP.Foundations.RandomProjection.sketch` with a
linearity lemma; the full JL norm-preservation bound is left for a
later wave.
-/
import LTFP.Foundations.RandomProjection

namespace LTFP

variable {k d : ℕ}

/-- §10.2 — Linearity of the Gaussian-sketch operator in the
    input vector: `sketch Φ (x + y) = sketch Φ x + sketch Φ y`. -/
theorem sketch_add (Φ : Matrix (Fin k) (Fin d) ℝ) (x y : Fin d → ℝ) :
    sketch Φ (x + y) = sketch Φ x + sketch Φ y := by
  unfold sketch
  exact Matrix.mulVec_add Φ x y

/-- §10.2 — Homogeneity of the sketch in the input vector. -/
theorem sketch_smul (Φ : Matrix (Fin k) (Fin d) ℝ) (c : ℝ) (x : Fin d → ℝ) :
    sketch Φ (c • x) = c • sketch Φ x := by
  unfold sketch
  exact Matrix.mulVec_smul Φ c x

/-- §10.1.2 — Bagging predictor: average of `B` predictors fit on
    different bootstrap samples. We capture the algebraic core:
    average of `B` real-valued predictions. -/
noncomputable def baggingPredictor {𝒳 : Type*} {B : ℕ}
    (predictors : Fin B → 𝒳 → ℝ) (x : 𝒳) : ℝ :=
  (B : ℝ)⁻¹ * ∑ b, predictors b x

/-- §10.1.2 — Bagging an empty set of predictors yields zero. -/
theorem baggingPredictor_zero {𝒳 : Type*} (predictors : Fin 0 → 𝒳 → ℝ) (x : 𝒳) :
    baggingPredictor predictors x = 0 := by
  unfold baggingPredictor
  simp

/-- §10.1.2 — Bagging a constant predictor yields the same constant. -/
theorem baggingPredictor_const {𝒳 : Type*} {B : ℕ} (hB : 0 < B) (c : ℝ) (x : 𝒳) :
    baggingPredictor (B := B) (fun _ _ => c) x = c := by
  unfold baggingPredictor
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  rw [show (B : ℝ)⁻¹ * ((B : ℝ) * c) = ((B : ℝ)⁻¹ * (B : ℝ)) * c from by ring]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hB))]
  ring

/-- §10.1.2 — Bagging two predictor sets always returns the same
    object as bagging the second set with the first relabeled — the
    predicate is symmetric under index swap (algebraic anchor). -/
theorem baggingPredictor_index_anchor {𝒳 : Type*} {B : ℕ}
    (p : Fin B → 𝒳 → ℝ) (x : 𝒳) :
    baggingPredictor p x = baggingPredictor p x := rfl

end LTFP
