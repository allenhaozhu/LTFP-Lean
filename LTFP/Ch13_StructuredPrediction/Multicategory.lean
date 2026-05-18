/-
LTFP §13.1 — Multicategory classification.

Bach (2024) §13.1, pp. 380-386. With `k` classes `𝒴 = {1, …, k}`,
a predictor `f : 𝒳 → 𝒴` and the 0-1 loss yields
`R(f) = ℙ(f(x) ≠ y)`. As in binary classification (Ch 4), one
typically learns a *score function* `g : 𝒳 → ℝᵏ` and predicts
`f(x) = argmax_j g(x)_j`.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

namespace LTFP

variable {k : ℕ}

/-- §13.1 — Multicategory 0-1 loss: 1 if prediction differs from
    the true label, 0 otherwise. -/
def multicategoryLoss (yhat y : Fin k) : ℝ :=
  if yhat = y then 0 else 1

/-- §13.1 sanity lemma: multicategory loss is nonnegative. -/
theorem multicategoryLoss_nonneg (yhat y : Fin k) :
    0 ≤ multicategoryLoss yhat y := by
  unfold multicategoryLoss
  split_ifs <;> norm_num

/-- §13.1 sanity lemma: multicategory loss vanishes exactly on
    correct predictions. -/
theorem multicategoryLoss_eq_zero_iff (yhat y : Fin k) :
    multicategoryLoss yhat y = 0 ↔ yhat = y := by
  unfold multicategoryLoss
  split_ifs with h
  · simp [h]
  · simp [h]

/-- §13.1 — Multicategory loss is symmetric in its arguments. -/
theorem multicategoryLoss_symm (yhat y : Fin k) :
    multicategoryLoss yhat y = multicategoryLoss y yhat := by
  unfold multicategoryLoss
  by_cases h : yhat = y
  · simp [h]
  · have h' : y ≠ yhat := fun heq => h heq.symm
    simp [h, h']

/-- §13.1 — Multicategory loss is bounded by 1. -/
theorem multicategoryLoss_le_one (yhat y : Fin k) :
    multicategoryLoss yhat y ≤ 1 := by
  unfold multicategoryLoss
  split_ifs <;> norm_num

/-- §13.1 — Diagonal: multicategoryLoss y y = 0. -/
theorem multicategoryLoss_diag (y : Fin k) :
    multicategoryLoss y y = 0 := by
  unfold multicategoryLoss; simp

/-- §13.1 — Multicategory loss is `0` or `1` (binary indicator). -/
theorem multicategoryLoss_zero_or_one (yhat y : Fin k) :
    multicategoryLoss yhat y = 0 ∨ multicategoryLoss yhat y = 1 := by
  unfold multicategoryLoss
  split_ifs <;> simp

/-- §13.1 — Multicategory loss equals 1 iff prediction is wrong. -/
theorem multicategoryLoss_eq_one_iff (yhat y : Fin k) :
    multicategoryLoss yhat y = 1 ↔ yhat ≠ y := by
  unfold multicategoryLoss
  split_ifs with h
  · simp [h]
  · simp [h]

/-- §13.1 — Multicategory loss in [0, 1]. -/
theorem multicategoryLoss_in_unit (yhat y : Fin k) :
    0 ≤ multicategoryLoss yhat y ∧ multicategoryLoss yhat y ≤ 1 :=
  ⟨multicategoryLoss_nonneg _ _, multicategoryLoss_le_one _ _⟩

/-- §13.2 — *Multi-label* binary loss: with `k` independent binary
    tags, the loss is the Hamming distance between predicted and
    true label vectors `Fin k → Bool`. Equivalently, the sum of
    per-label 0-1 indicators (Bach 2024 §13.2, p. 387). -/
def multilabelLoss (yhat y : Fin k → Bool) : ℝ :=
  ∑ j, (if yhat j = y j then (0 : ℝ) else 1)

/-- §13.2 — Multi-label loss is nonnegative (each summand is). -/
theorem multilabelLoss_nonneg (yhat y : Fin k → Bool) :
    0 ≤ multilabelLoss yhat y := by
  unfold multilabelLoss
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> norm_num

/-- §13.2 — Multi-label loss is bounded by the number of labels `k`. -/
theorem multilabelLoss_le_k (yhat y : Fin k → Bool) :
    multilabelLoss yhat y ≤ (k : ℝ) := by
  unfold multilabelLoss
  have h : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      (if yhat j = y j then (0 : ℝ) else 1) ≤ 1 := by
    intro j _
    split_ifs <;> norm_num
  calc ∑ j, (if yhat j = y j then (0 : ℝ) else 1)
      ≤ ∑ _j : Fin k, (1 : ℝ) := Finset.sum_le_sum h
    _ = (k : ℝ) := by simp

/-- §13.2 — Multi-label loss vanishes exactly on full agreement. The
    Hamming distance is zero iff every coordinate matches. -/
theorem multilabelLoss_eq_zero_iff (yhat y : Fin k → Bool) :
    multilabelLoss yhat y = 0 ↔ ∀ j, yhat j = y j := by
  unfold multilabelLoss
  constructor
  · intro hsum j
    by_contra hne
    have hpos : (if yhat j = y j then (0 : ℝ) else 1) > 0 := by
      simp [hne]
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        0 ≤ (if yhat i = y i then (0 : ℝ) else 1) := by
      intro i _; split_ifs <;> norm_num
    have hzero : (if yhat j = y j then (0 : ℝ) else 1) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ _)
    linarith
  · intro hall
    apply Finset.sum_eq_zero
    intro j _
    simp [hall j]

end LTFP
