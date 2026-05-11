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

namespace LTFP

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

end LTFP
