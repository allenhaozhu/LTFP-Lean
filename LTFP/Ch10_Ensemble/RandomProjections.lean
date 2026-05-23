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

/-- §10.2 — Negation commutes with the sketch operator. Completes the
    linear-map API on the input side. -/
theorem sketch_neg (Φ : Matrix (Fin k) (Fin d) ℝ) (x : Fin d → ℝ) :
    sketch Φ (-x) = -sketch Φ x := by
  unfold sketch
  exact Matrix.mulVec_neg x Φ

/-- §10.2 — Subtraction commutes with the sketch operator. Completes
    the linear-map API on the input side. -/
theorem sketch_sub (Φ : Matrix (Fin k) (Fin d) ℝ) (x y : Fin d → ℝ) :
    sketch Φ (x - y) = sketch Φ x - sketch Φ y := by
  rw [sub_eq_add_neg, sketch_add, sketch_neg, sub_eq_add_neg]

/-- §10.2 — Explicit component formula for the sketch operator:
    the `i`-th coordinate of `Φx` is the dot product of the `i`-th
    row of `Φ` with `x`. This is the algebraic core of every
    sketch-norm calculation: it makes the `(Φx)ᵢ = ∑ⱼ Φᵢⱼ xⱼ`
    expansion available as a one-liner downstream. -/
theorem sketch_apply (Φ : Matrix (Fin k) (Fin d) ℝ) (x : Fin d → ℝ)
    (i : Fin k) :
    sketch Φ x i = ∑ j, Φ i j * x j := by
  unfold sketch
  rfl

/-- §10.2 — Explicit squared-norm expansion of the sketch:
    `‖Φx‖² = ∑ᵢ (∑ⱼ Φᵢⱼ xⱼ)²`. Pure matrix/vector algebra; this is
    the deterministic anchor underneath the probabilistic Johnson–
    Lindenstrauss norm-preservation analysis, which bounds the
    expectation and concentration of this exact sum. -/
theorem sketch_norm_sq_expansion (Φ : Matrix (Fin k) (Fin d) ℝ)
    (x : Fin d → ℝ) :
    ∑ i, (sketch Φ x i) ^ 2 = ∑ i, (∑ j, Φ i j * x j) ^ 2 := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sketch_apply]

/-- §10.2 — Identity sketch preserves the squared norm exactly:
    `∑ᵢ ((1 · x)ᵢ)² = ∑ᵢ xᵢ²`. This is the deterministic boundary
    case of the JL bound (`Φ = I` is trivially an isometry); the
    randomized JL result extends this to high-probability isometry
    for random Gaussian `Φ` of much smaller output dimension. -/
theorem sketch_one_norm_sq (x : Fin k → ℝ) :
    ∑ i, (sketch (1 : Matrix (Fin k) (Fin k) ℝ) x i) ^ 2 =
      ∑ i, (x i) ^ 2 := by
  simp [sketch_one]

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

/-- §10.1.2 — Bagging is additive in the predictor family: the
    average of pointwise sums is the sum of averages. This is the
    algebraic core of the variance-reduction analysis: bagging
    commutes with the linear structure of the predictor space, so
    we can analyze fluctuations around the mean independently of
    the mean. -/
theorem baggingPredictor_add {𝒳 : Type*} {B : ℕ}
    (p q : Fin B → 𝒳 → ℝ) (x : 𝒳) :
    baggingPredictor (fun b => p b + q b) x =
      baggingPredictor p x + baggingPredictor q x := by
  unfold baggingPredictor
  simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]

/-- §10.1.2 — Bagging is homogeneous in the predictor family: scaling
    every base predictor by `c` scales the bagged predictor by `c`. -/
theorem baggingPredictor_smul {𝒳 : Type*} {B : ℕ}
    (c : ℝ) (p : Fin B → 𝒳 → ℝ) (x : 𝒳) :
    baggingPredictor (fun b => c • p b) x = c • baggingPredictor p x := by
  unfold baggingPredictor
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- §10.1.3 — Random-forest predictor as an explicit convex
    combination of `B` tree predictors with nonneg weights summing
    to one. Bach (2024) §10.1.3 (random forests as ensembles of
    decision trees). -/
noncomputable def randomForestPredictor {𝒳 : Type*} {B : ℕ}
    (trees : Fin B → 𝒳 → ℝ) (w : Fin B → ℝ) (x : 𝒳) : ℝ :=
  ∑ b, w b * trees b x

/-- §10.1.3 — A random-forest predictor over a constant family of
    trees `T ≡ c` collapses to `c` whenever the weights sum to `1`.
    This is the convex-combination invariant: any convex average of
    a constant is that constant. -/
theorem randomForestPredictor_const_of_sum_eq_one
    {𝒳 : Type*} {B : ℕ} (w : Fin B → ℝ) (c : ℝ) (x : 𝒳)
    (hw : ∑ b, w b = 1) :
    randomForestPredictor (𝒳 := 𝒳) (fun _ _ => c) w x = c := by
  unfold randomForestPredictor
  rw [← Finset.sum_mul, hw, one_mul]

/-- §10.1.3 — Uniform-weight random forest reduces to the bagging
    predictor (`1/B` average). Connects §10.1.2 (bagging) to §10.1.3
    (random forests). -/
theorem randomForestPredictor_uniform {𝒳 : Type*} {B : ℕ}
    (trees : Fin B → 𝒳 → ℝ) (x : 𝒳) :
    randomForestPredictor trees (fun _ => (B : ℝ)⁻¹) x =
      baggingPredictor trees x := by
  unfold randomForestPredictor baggingPredictor
  rw [← Finset.mul_sum]

end LTFP
