/-
LTFP §10.3 — Boosting.

Bach (2024) §10.3, pp. 298-310. Boosting incrementally builds an
additive model `Fₜ(x) = ∑ₜ αₜ · hₜ(x)` of weak learners `hₜ`. The
AdaBoost algorithm (§10.3.4) optimizes the exponential surrogate
`Φ(u) = exp(-u)`.
-/
import LTFP.Ch04_ERM.Convexification
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Exp

namespace LTFP

open Real

variable {𝒳 : Type*} {T : ℕ}

/-- §10.3 — Boosted predictor: weighted sum of `T` weak learners. -/
def boostedPredictor
    (h : Fin T → 𝒳 → ℝ) (α : Fin T → ℝ) (x : 𝒳) : ℝ :=
  ∑ t, α t * h t x

/-- §10.3 sanity lemma: a boosted predictor with `T = 0` is identically 0. -/
theorem boostedPredictor_zero_steps
    (h : Fin 0 → 𝒳 → ℝ) (α : Fin 0 → ℝ) (x : 𝒳) :
    boostedPredictor h α x = 0 := by
  unfold boostedPredictor
  simp

/-- §10.3 — A boosted predictor is linear in the coefficients `α`. -/
theorem boostedPredictor_add_α
    (h : Fin T → 𝒳 → ℝ) (α β : Fin T → ℝ) (x : 𝒳) :
    boostedPredictor h (α + β) x = boostedPredictor h α x + boostedPredictor h β x := by
  simp only [boostedPredictor, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- §10.3 — Boosted predictor is homogeneous in the coefficients. -/
theorem boostedPredictor_smul_α
    (h : Fin T → 𝒳 → ℝ) (c : ℝ) (α : Fin T → ℝ) (x : 𝒳) :
    boostedPredictor h (c • α) x = c * boostedPredictor h α x := by
  simp only [boostedPredictor, Pi.smul_apply, smul_eq_mul, mul_assoc,
             ← Finset.mul_sum]

/-- §10.3 — Boosting with all-zero coefficients yields zero predictions. -/
theorem boostedPredictor_zero_coeffs
    (h : Fin T → 𝒳 → ℝ) (x : 𝒳) :
    boostedPredictor h (fun _ => 0) x = 0 := by
  unfold boostedPredictor
  simp

/-- §10.3 — Boosting with constant zero weak learners yields zero. -/
theorem boostedPredictor_zero_h
    (α : Fin T → ℝ) (x : 𝒳) :
    boostedPredictor (𝒳 := 𝒳) (fun _ _ => 0) α x = 0 := by
  unfold boostedPredictor
  simp

/-- §10.3 — A boosted predictor with single weak learner is just
    `α 0 · h 0 x`. -/
theorem boostedPredictor_one_step
    (h : Fin 1 → 𝒳 → ℝ) (α : Fin 1 → ℝ) (x : 𝒳) :
    boostedPredictor h α x = α 0 * h 0 x := by
  unfold boostedPredictor
  simp

/-- §10.3 — Boosted predictor expansion (definitional unfold). -/
theorem boostedPredictor_eq
    (h : Fin T → 𝒳 → ℝ) (α : Fin T → ℝ) (x : 𝒳) :
    boostedPredictor h α x = ∑ t, α t * h t x := rfl

/-- §10.3 — Negating the coefficient sequence negates the boosted
    predictor. A direct corollary of linearity, useful when the AdaBoost
    update flips the sign of `αₜ` on misclassified rounds. -/
theorem boostedPredictor_neg_α
    (h : Fin T → 𝒳 → ℝ) (α : Fin T → ℝ) (x : 𝒳) :
    boostedPredictor h (-α) x = -boostedPredictor h α x := by
  simp only [boostedPredictor, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- §10.3 — Linearity under subtraction of coefficient sequences. -/
theorem boostedPredictor_sub_α
    (h : Fin T → 𝒳 → ℝ) (α β : Fin T → ℝ) (x : 𝒳) :
    boostedPredictor h (α - β) x =
      boostedPredictor h α x - boostedPredictor h β x := by
  simp only [boostedPredictor, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- §10.3.4 — AdaBoost reweighting factor for a sample with margin
    `y · h(x)`: `w' = w · exp(-α · y · h(x))`. Bach (2024) eq. (10.27). -/
noncomputable def adaBoostWeight (w α m : ℝ) : ℝ :=
  w * Real.exp (-(α * m))

/-- §10.3.4 — AdaBoost reweighting preserves positivity: if the prior
    weight `w` is positive, so is the next-round weight. This is the
    invariant that lets us renormalize into a probability distribution
    on the training set. -/
theorem adaBoostWeight_pos {w α m : ℝ} (hw : 0 < w) :
    0 < adaBoostWeight w α m := by
  unfold adaBoostWeight
  exact mul_pos hw (Real.exp_pos _)

/-- §10.3.4 — AdaBoost reweighting with zero step `α = 0` keeps the
    weight unchanged: `adaBoostWeight w 0 m = w`. -/
theorem adaBoostWeight_zero_step (w m : ℝ) :
    adaBoostWeight w 0 m = w := by
  unfold adaBoostWeight
  simp [Real.exp_zero]

/-- §10.3 — The exponential of a boosted predictor splits as a product
    of per-round exponentials: `exp(F_T(x)) = ∏ₜ exp(αₜ · hₜ(x))`. This is
    the algebraic identity that turns the AdaBoost exponential surrogate
    objective into a product-of-margin form on each training sample. -/
theorem exp_boostedPredictor_eq_prod
    (h : Fin T → 𝒳 → ℝ) (α : Fin T → ℝ) (x : 𝒳) :
    Real.exp (boostedPredictor h α x) = ∏ t, Real.exp (α t * h t x) := by
  unfold boostedPredictor
  rw [Real.exp_sum]

end LTFP
