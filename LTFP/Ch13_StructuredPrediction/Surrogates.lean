/-
LTFP §13.3 — Surrogate methods for structured prediction.

Bach (2024) §13.3, pp. 391-393. A *score function* `g : 𝒳 → ℝᵏ`
maps each input to a k-vector of real-valued scores; the predicted
class is `argmax_j g(x)_j`. The Φ-risk for structured prediction
generalizes the binary surrogate framework of Ch 4.
-/
import LTFP.Ch13_StructuredPrediction.Multicategory
import Mathlib.Tactic.Linarith

namespace LTFP

variable {k : ℕ}

/-- §13.3 — Predicate: a class label `yhat` is **a** valid argmax of
    a score vector `g`, i.e. `g yhat ≥ g j` for every `j`. We work
    with this predicate rather than choosing a canonical argmax to
    avoid `Finite.exists_max`-style boilerplate. -/
def IsArgmax (g : Fin k → ℝ) (yhat : Fin k) : Prop :=
  ∀ j, g j ≤ g yhat

/-- §13.3 — Score-vector loss: applied to a witnessed argmax decoding. -/
def scoreLoss (g : Fin k → ℝ) (yhat y : Fin k) (_ : IsArgmax g yhat) : ℝ :=
  multicategoryLoss yhat y

/-- §13.3 sanity lemma: the score loss is nonnegative everywhere. -/
theorem scoreLoss_nonneg (g : Fin k → ℝ) (yhat y : Fin k)
    (h : IsArgmax g yhat) :
    0 ≤ scoreLoss g yhat y h := multicategoryLoss_nonneg _ _

/-- §13.5 — Max-margin (structured SVM) framework: a score vector
    has *margin* `γ` on `(x, y)` iff `g(x)_y - g(x)_j ≥ γ` for all
    `j ≠ y`. We capture the *margin satisfied at level γ* predicate. -/
def MarginSatisfied (g : Fin k → ℝ) (y : Fin k) (γ : ℝ) : Prop :=
  ∀ j, j ≠ y → g j + γ ≤ g y

/-- §13.5 sanity lemma: zero margin is automatic when `y` is a strict
    argmax. -/
theorem MarginSatisfied_zero (g : Fin k → ℝ) (y : Fin k)
    (h : ∀ j, j ≠ y → g j ≤ g y) :
    MarginSatisfied g y 0 := by
  intro j hj
  simpa using h j hj

/-- §13.5 — Margin satisfaction is monotone in `γ` (smaller margin
    requirement is easier to satisfy). -/
theorem MarginSatisfied.mono {g : Fin k → ℝ} {y : Fin k} {γ γ' : ℝ}
    (h : MarginSatisfied g y γ) (hγ : γ' ≤ γ) :
    MarginSatisfied g y γ' := fun j hj => by
  have h₁ : g j + γ ≤ g y := h j hj
  have h₂ : g j + γ' ≤ g j + γ := by
    have := add_le_add_right hγ (g j)
    -- this : γ' + g j ≤ γ + g j
    linarith
  exact h₂.trans h₁

end LTFP
