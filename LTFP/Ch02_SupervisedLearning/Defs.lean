/-
LTFP §2.2 — Supervised learning: loss, risk, Bayes predictor.

Bach (2024), *Learning Theory from First Principles*, §2.2, pp. 25–29.

A loss function compares a prediction to the truth; the population risk is
its expectation under the data distribution; a Bayes predictor minimizes the
population risk; the Bayes risk is that minimum.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace LTFP

open MeasureTheory

/-- §2.2.1 — A loss function `ℓ : 𝒵 → 𝒴 → ℝ` compares a prediction in `𝒵`
    to a label in `𝒴`. We use the curried convention so that `ℓ z y` is
    the loss of predicting `z` when the truth is `y`. -/
@[reducible] def LossFunction (𝒴 : Type*) (𝒵 : Type*) : Type _ := 𝒵 → 𝒴 → ℝ

variable {𝒳 𝒴 𝒵 : Type*}

/-- §2.2.2 — Population risk `R(f) = 𝔼[ℓ(f(x), y)]` under a joint
    distribution `D` on `𝒳 × 𝒴`. -/
noncomputable def populationRisk
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴)) (f : 𝒳 → 𝒵) : ℝ :=
  ∫ p, ℓ (f p.1) p.2 ∂D

/-- §2.2.3 — A Bayes predictor: any pointwise minimizer of `populationRisk`. -/
def bayesPredictor
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴)) (fstar : 𝒳 → 𝒵) : Prop :=
  ∀ f : 𝒳 → 𝒵, populationRisk ℓ D fstar ≤ populationRisk ℓ D f

/-- §2.2.3 — Bayes risk: the infimum of `populationRisk` over all predictors. -/
noncomputable def bayesRisk
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴)) : ℝ :=
  ⨅ f : 𝒳 → 𝒵, populationRisk ℓ D f

/-- §2.2.3 — A Bayes predictor attains the Bayes risk. -/
theorem bayesRisk_isLeast
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [Nonempty 𝒵]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴))
    {fstar : 𝒳 → 𝒵} (h : bayesPredictor ℓ D fstar) :
    populationRisk ℓ D fstar = bayesRisk ℓ D := by
  apply le_antisymm
  · exact le_ciInf h
  · refine ciInf_le ?_ fstar
    refine ⟨populationRisk ℓ D fstar, ?_⟩
    rintro _ ⟨g, rfl⟩
    exact h g

/-- §2.2.2 — Squared loss `ℓ(z, y) = (z − y)²` for real-valued
    regression. -/
def squareLoss : LossFunction ℝ ℝ := fun z y => (z - y)^2

/-- §2.2.2 — Squared loss is nonnegative. -/
theorem squareLoss_nonneg (z y : ℝ) : 0 ≤ squareLoss z y := by
  unfold squareLoss; exact sq_nonneg _

/-- §2.2.2 — Squared loss is symmetric in its arguments
    (since `(z − y)² = (y − z)²`). -/
theorem squareLoss_symm (z y : ℝ) : squareLoss z y = squareLoss y z := by
  unfold squareLoss
  ring

/-- §2.2.2 — Squared loss vanishes exactly when prediction = truth. -/
theorem squareLoss_eq_zero_iff (z y : ℝ) : squareLoss z y = 0 ↔ z = y := by
  unfold squareLoss
  rw [sq_eq_zero_iff, sub_eq_zero]

/-- §2.2.2 — Squared loss is `0` on the diagonal. -/
theorem squareLoss_self (y : ℝ) : squareLoss y y = 0 := by
  unfold squareLoss; ring

/-- §2.2.2 — Squared loss explicit value. -/
theorem squareLoss_eq_sq_diff (z y : ℝ) : squareLoss z y = (z - y)^2 := rfl

/-- §2.2.2 — Squared loss is convex in `z` (algebraic core: difference is
    polynomial of degree 2 with positive leading coefficient). -/
theorem squareLoss_convex_anchor (z₁ z₂ y : ℝ) :
    squareLoss ((z₁ + z₂) / 2) y ≤
      (squareLoss z₁ y + squareLoss z₂ y) / 2 := by
  unfold squareLoss
  nlinarith [sq_nonneg (z₁ - z₂)]

/-- §2.2.1 — Constant-zero loss function. -/
def zeroLoss : LossFunction Bool Bool := fun _ _ => 0

/-- §2.2.1 — Zero loss is nonneg. -/
theorem zeroLoss_nonneg (z y : Bool) : 0 ≤ zeroLoss z y := le_refl 0

/-- §2.2.2 — Population risk equals the Bochner integral of the loss
    against the joint distribution. This is the bridge from the
    LTFP-namespace `populationRisk` to the Mathlib `MeasureTheory`
    integration framework. -/
theorem populationRisk_eq_integral
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴)) (f : 𝒳 → 𝒵) :
    populationRisk ℓ D f = ∫ p, ℓ (f p.1) p.2 ∂D := rfl

/-- §2.2.2 — Population risk under the zero measure is zero. -/
theorem populationRisk_zero_measure
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (ℓ : LossFunction 𝒴 𝒵) (f : 𝒳 → 𝒵) :
    populationRisk ℓ (0 : Measure (𝒳 × 𝒴)) f = 0 := by
  unfold populationRisk
  simp

/-- §2.2.2 — Population risk of a nonneg loss is nonneg. -/
theorem populationRisk_nonneg
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    {ℓ : LossFunction 𝒴 𝒵} (hℓ : ∀ z y, 0 ≤ ℓ z y)
    (D : Measure (𝒳 × 𝒴)) (f : 𝒳 → 𝒵) :
    0 ≤ populationRisk ℓ D f := by
  unfold populationRisk
  exact integral_nonneg (fun p => hℓ _ _)

/-- §2.2.3 — Bayes risk is at most any specific population risk.
    This is the key composition theorem: every predictor `f`
    individually contributes to the infimum, so `bayesRisk ≤ R(f)`.
    Used everywhere — every excess-risk argument uses it implicitly.
    Real proof via `ciInf_le` and a `BddBelow` witness. -/
theorem bayesRisk_le_populationRisk
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [Nonempty 𝒵]
    {ℓ : LossFunction 𝒴 𝒵} (hℓ : ∀ z y, 0 ≤ ℓ z y)
    (D : Measure (𝒳 × 𝒴)) (f : 𝒳 → 𝒵) :
    bayesRisk ℓ D ≤ populationRisk ℓ D f := by
  unfold bayesRisk
  refine ciInf_le ?_ f
  refine ⟨0, ?_⟩
  rintro _ ⟨g, rfl⟩
  exact populationRisk_nonneg hℓ D g

/-- §2.2.3 — Bayes risk is nonneg under nonneg loss. -/
theorem bayesRisk_nonneg
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [Nonempty 𝒵]
    {ℓ : LossFunction 𝒴 𝒵} (hℓ : ∀ z y, 0 ≤ ℓ z y)
    (D : Measure (𝒳 × 𝒴)) :
    0 ≤ bayesRisk ℓ D := by
  unfold bayesRisk
  refine le_ciInf ?_
  intro f
  exact populationRisk_nonneg hℓ D f

/-- §2.2.3 — Excess risk is nonneg for any predictor (under nonneg loss). -/
theorem excess_risk_nonneg
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [Nonempty 𝒵]
    {ℓ : LossFunction 𝒴 𝒵} (hℓ : ∀ z y, 0 ≤ ℓ z y)
    (D : Measure (𝒳 × 𝒴)) (f : 𝒳 → 𝒵) :
    0 ≤ populationRisk ℓ D f - bayesRisk ℓ D := by
  have h := bayesRisk_le_populationRisk hℓ D f
  linarith

/-- §2.2.2 — **Triangle-style bound for squared loss.** For any
    intermediate point `a`, `(z − y)² ≤ 2 (z − a)² + 2 (a − y)²`.
    This is the standard "split through an anchor" inequality used to
    convert pointwise-loss bounds into squared-loss bounds (Bach 2024,
    §2.2; appears repeatedly in regression-style oracle inequalities).
    Pure algebra: expand both sides and apply `(z − a) + (a − y) = z − y`
    with `(u + v)² ≤ 2 u² + 2 v²`. -/
theorem squareLoss_triangle (z a y : ℝ) :
    squareLoss z y ≤ 2 * squareLoss z a + 2 * squareLoss a y := by
  unfold squareLoss
  nlinarith [sq_nonneg ((z - a) - (a - y)), sq_nonneg (z - y),
             sq_nonneg (z - a), sq_nonneg (a - y)]

/-- §2.2.3 — **Bayes predictors are unique up to risk.** Any two
    Bayes predictors `f*` and `g*` produce the same population risk.
    The Bayes risk is well-defined regardless of which minimizer is
    selected (Bach 2024, §2.2.3). -/
theorem bayesPredictor_unique_risk
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    {ℓ : LossFunction 𝒴 𝒵} {D : Measure (𝒳 × 𝒴)}
    {fstar gstar : 𝒳 → 𝒵}
    (hf : bayesPredictor ℓ D fstar) (hg : bayesPredictor ℓ D gstar) :
    populationRisk ℓ D fstar = populationRisk ℓ D gstar := by
  exact le_antisymm (hf gstar) (hg fstar)

end LTFP
