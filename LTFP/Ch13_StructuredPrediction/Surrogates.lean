/-
LTFP §13.3 — Surrogate methods for structured prediction.

Bach (2024) §13.3, pp. 391-393. A *score function* `g : 𝒳 → ℝᵏ`
maps each input to a k-vector of real-valued scores; the predicted
class is `argmax_j g(x)_j`. The Φ-risk for structured prediction
generalizes the binary surrogate framework of Ch 4.
-/
import LTFP.Ch13_StructuredPrediction.Multicategory
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

/-- §13.5 — If the score vector has a *positive* margin on `(x, y)`,
    then the true label `y` is itself a valid argmax. This is the
    fundamental link between max-margin learning and the underlying
    0-1 classifier (Bach 2024 §13.5, p. 392, eq. 13.16). -/
theorem MarginSatisfied.isArgmax {g : Fin k → ℝ} {y : Fin k} {γ : ℝ}
    (hγ : 0 ≤ γ) (h : MarginSatisfied g y γ) :
    IsArgmax g y := by
  intro j
  by_cases hjy : j = y
  · subst hjy; exact le_refl _
  · have h₁ : g j + γ ≤ g y := h j hjy
    linarith

/-- §13.5 — Margin is *invariant under uniform shift* of the score
    vector. Adding the same constant `c` to every coordinate leaves
    every pairwise margin `g y - g j` unchanged, so the margin
    predicate is preserved (Bach 2024 §13.5, p. 392, scale-invariance
    discussion preceding eq. 13.18). -/
theorem MarginSatisfied.shift {g : Fin k → ℝ} {y : Fin k} {γ : ℝ}
    (h : MarginSatisfied g y γ) (c : ℝ) :
    MarginSatisfied (fun j => g j + c) y γ := by
  intro j hj
  have h₁ : g j + γ ≤ g y := h j hj
  linarith

/-- §13.5 — Margin scales linearly under *positive scaling* of the
    score vector: if `g` has margin `γ` at `y`, then `α • g` has
    margin `α γ` at `y` for any `α ≥ 0` (Bach 2024 §13.5, p. 392,
    homogeneity of the margin functional). -/
theorem MarginSatisfied.smul_nonneg {g : Fin k → ℝ} {y : Fin k} {γ : ℝ}
    (h : MarginSatisfied g y γ) {α : ℝ} (hα : 0 ≤ α) :
    MarginSatisfied (fun j => α * g j) y (α * γ) := by
  intro j hj
  show α * g j + α * γ ≤ α * g y
  have h₁ : g j + γ ≤ g y := h j hj
  have h₂ : α * (g j + γ) ≤ α * g y := mul_le_mul_of_nonneg_left h₁ hα
  have h₃ : α * (g j + γ) = α * g j + α * γ := by ring
  linarith

/-- §13.5 — *Constant scores have zero margin.* If every coordinate
    of `g` equals the same value, then `g` satisfies a margin of
    `γ = 0` at any label `y`. This is the degenerate base case used
    in Bach 2024 §13.5 when discussing the necessity of strict
    margins for separability (p. 392, eq. 13.17). -/
theorem MarginSatisfied.const (c : ℝ) (y : Fin k) :
    MarginSatisfied (fun _ : Fin k => c) y 0 := by
  intro j _
  simp

end LTFP
