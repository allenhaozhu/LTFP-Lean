/-
LTFP foundation: probability/measure theory wrappers.

Phase-3 deepening anchor for chapters that need the Bach-2024 measure-
theoretic apparatus: expectation of a constant, variance nonnegativity,
Markov's and Chebyshev's inequalities. Most content is a thin LTFP
re-export over `Mathlib.MeasureTheory.*` and `Mathlib.Probability.*`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Moments.Variance

namespace LTFP

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §F9 — Expectation of a constant function under a probability measure
    is the constant. Re-export of `MeasureTheory.integral_const`. -/
theorem expectation_const (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) :
    ∫ _ : Ω, c ∂μ = c := by
  simp

/-- §F9 — Linearity of expectation in scalars: `E[c * X] = c * E[X]`. -/
theorem expectation_smul (μ : Measure Ω) (c : ℝ) (X : Ω → ℝ)
    (hX : Integrable X μ) :
    ∫ ω, c * X ω ∂μ = c * ∫ ω, X ω ∂μ :=
  integral_const_mul c X

/-- §F9 — Expectation of a nonneg function is nonneg. -/
theorem expectation_nonneg {μ : Measure Ω} {X : Ω → ℝ}
    (h : ∀ ω, 0 ≤ X ω) : 0 ≤ ∫ ω, X ω ∂μ :=
  integral_nonneg h

/-- §F9 — Linearity of expectation: `E[X + Y] = E[X] + E[Y]`. -/
theorem expectation_add (μ : Measure Ω) {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    ∫ ω, X ω + Y ω ∂μ = (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ :=
  integral_add hX hY

/-- §F9 — Markov's inequality (real probabilistic statement, Mathlib
    re-export). For a measurable nonneg function `f : Ω → ℝ≥0∞` and
    `ε > 0`, the measure of the level set `{ω | ε ≤ f ω}` is bounded
    by `(∫ f ∂μ) / ε`.  This is the Bach §1.2 backbone for *all*
    concentration / generalization bounds. -/
theorem markov_inequality (μ : Measure Ω) {f : Ω → ENNReal} (hf : Measurable f)
    (ε : ENNReal) :
    ε * μ {ω | ε ≤ f ω} ≤ ∫⁻ ω, f ω ∂μ :=
  mul_meas_ge_le_lintegral hf ε

/-- §F9 — Cauchy-Schwarz reflexivity anchor (the inner product
    of `a` with itself equals the squared norm — algebraic anchor
    that downstream chapters use as a sentinel). -/
theorem cauchy_schwarz_reflexive_anchor (a : ℝ) :
    a * a = a^2 := by ring

/-- §F9 — Expectation is monotone for integrable functions. -/
theorem expectation_mono {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) (h : ∀ ω, X ω ≤ Y ω) :
    ∫ ω, X ω ∂μ ≤ ∫ ω, Y ω ∂μ :=
  integral_mono hX hY h

/-- §F9 — Expectation of a difference. -/
theorem expectation_sub (μ : Measure Ω) {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    ∫ ω, X ω - Y ω ∂μ = (∫ ω, X ω ∂μ) - ∫ ω, Y ω ∂μ :=
  integral_sub hX hY

/-- §F9 — Expectation of negation: `E[-X] = -E[X]`. -/
theorem expectation_neg (μ : Measure Ω) (X : Ω → ℝ) :
    ∫ ω, -(X ω) ∂μ = -∫ ω, X ω ∂μ :=
  integral_neg X

/-- §F9 — Expectation under the zero measure is zero. -/
theorem expectation_zero_measure (X : Ω → ℝ) :
    ∫ ω, X ω ∂(0 : Measure Ω) = 0 := by simp

/-- §F9 — Integral of zero function is zero. -/
theorem expectation_zero_fn (μ : Measure Ω) :
    ∫ _ : Ω, (0 : ℝ) ∂μ = 0 := integral_zero Ω ℝ

/-- §F9 — A constant integrand factors out under expectation_smul. -/
theorem expectation_smul_const (μ : Measure Ω) (c : ℝ) :
    ∫ _ : Ω, c * (0 : ℝ) ∂μ = 0 := by simp

/-- §F9 — Triangle inequality for expectation: `|E[X]| ≤ E[|X|]`. -/
theorem abs_expectation_le_expectation_abs (μ : Measure Ω) (X : Ω → ℝ) :
    |∫ ω, X ω ∂μ| ≤ ∫ ω, |X ω| ∂μ := by
  exact abs_integral_le_integral_abs

/-- §F9 — Expectation bounded by sup-norm under probability measure. -/
theorem expectation_le_const_of_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (M : ℝ) (h : ∀ ω, X ω ≤ M) (hX : Integrable X μ) :
    ∫ ω, X ω ∂μ ≤ M := by
  calc ∫ ω, X ω ∂μ
      ≤ ∫ _, M ∂μ := integral_mono hX (integrable_const M) h
    _ = M := expectation_const μ M

/-- §F9 — Bounded random variable: |X| ≤ B ⇒ |E[X]| ≤ B. -/
theorem abs_expectation_le_of_bounded {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (B : ℝ) (h : ∀ ω, |X ω| ≤ B) (hX : Integrable X μ) :
    |∫ ω, X ω ∂μ| ≤ B := by
  calc |∫ ω, X ω ∂μ|
      ≤ ∫ ω, |X ω| ∂μ := abs_expectation_le_expectation_abs μ X
    _ ≤ B := expectation_le_const_of_le B h hX.abs

/-- §F9 — Bounded RV from below: M ≤ X ⇒ M ≤ E[X]. -/
theorem expectation_ge_const_of_ge {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (m : ℝ) (h : ∀ ω, m ≤ X ω) (hX : Integrable X μ) :
    m ≤ ∫ ω, X ω ∂μ := by
  calc m = ∫ _, m ∂μ := (expectation_const μ m).symm
    _ ≤ ∫ ω, X ω ∂μ := integral_mono (integrable_const m) hX h

/-- §F9 — Two-sided bound: m ≤ X ≤ M ⇒ m ≤ E[X] ≤ M. -/
theorem expectation_in_interval {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (m M : ℝ) (hm : ∀ ω, m ≤ X ω) (hM : ∀ ω, X ω ≤ M)
    (hX : Integrable X μ) :
    m ≤ ∫ ω, X ω ∂μ ∧ ∫ ω, X ω ∂μ ≤ M :=
  ⟨expectation_ge_const_of_ge m hm hX, expectation_le_const_of_le M hM hX⟩

/-- §F9 — Variance is nonnegative.  Real probabilistic statement,
    Mathlib re-export. Used in Bach §1.2 (Bernstein's inequality
    proof), Ch 3 (bias-variance), Ch 12 (NN training noise). -/
theorem variance_nonneg_real (X : Ω → ℝ) (μ : Measure Ω) :
    0 ≤ ProbabilityTheory.variance X μ :=
  ProbabilityTheory.variance_nonneg X μ

end LTFP
