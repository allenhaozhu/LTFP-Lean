/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import LTFP.MathlibExt.Probability.Distance.Pinsker

/-!
# Gaussian two-point KL identity (algebraic core)

Proposed Mathlib path: `Mathlib/InformationTheory/KullbackLeibler/Gaussian.lean`.
Proposed Mathlib namespace: `ProbabilityTheory`.

This module lands the **algebraic core** of the closed-form
Kullback–Leibler divergence between two univariate Gaussian
distributions with common variance:

`KL(N(μ₀, σ²) ‖ N(μ₁, σ²)) = (μ₀ - μ₁)² / (2 σ²)`,

packaged as a real-valued function `gaussianKLScalar Δ σ := Δ²/(2σ²)`
parametric in the mean separation `Δ = μ₀ - μ₁` and the common
standard deviation `σ > 0`. The fully measure-theoretic version
`klDiv (gaussianReal μ₀ v) (gaussianReal μ₁ v) = ENNReal.ofReal (...)`
is a multi-week port (no `klDiv` of `gaussianReal` is in Mathlib at the
pin `80732f7660`); the present file isolates the algebraic content so
that downstream consumers — in particular the Le Cam two-point
minimax-lower-bound chain of Bach (2024) §3.7 — can compose against
the scalar KL value without committing to a particular
measure-theoretic surface.

The companion module `LTFP/MathlibExt/Probability/Distance/Pinsker.lean`
supplies the Pinsker-bound function `pinskerBound x := √(x/2)`. The
composition lemma `gaussianTwoPointPinskerBound` evaluates the Pinsker
upper bound on the Gaussian-KL value:

`pinskerBound (gaussianKLScalar Δ σ) = |Δ| / (2 σ)`.

This is precisely the testing-side TV bound used in the Gaussian
two-point method: under two `N(μᵢ, σ²)` likelihoods with mean gap
`Δ`, the total-variation distance between the likelihoods satisfies
`TV ≤ |Δ| / (2σ)` (Pinsker; valid as a *bound* whether or not Δ ≤ σ).

## Main definitions

* `gaussianKLScalar Δ σ` — the scalar KL gap between two univariate
  Gaussians with mean separation `Δ` and common standard deviation `σ`,
  evaluated as `Δ² / (2 σ²)`.

## Main results

* `gaussianKLScalar_nonneg` — the Gaussian KL gap is nonnegative.
* `gaussianKLScalar_eq_zero_iff` — vanishes iff `Δ = 0`.
* `gaussianKLScalar_mono_delta_sq` — monotone in `Δ²`.
* `gaussianKLScalar_antitone_var` — antitone in `σ²` for fixed `Δ`.
* `gaussianTwoPointPinskerBound` — composing Pinsker with the Gaussian
  KL value yields `pinskerBound (gaussianKLScalar Δ σ) = |Δ| / (2 σ)`.

## References

* T. M. Cover, J. A. Thomas, *Elements of Information Theory*, 2nd ed.,
  Wiley, 2006, Eq. 2.6 (Gaussian KL).
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, Section 2.4 (Gaussian two-point method).
* F. Bach, *Learning Theory from First Principles*, MIT Press, 2024,
  §3.7 (Mourtada minimax lower bound for OLS).

## Tags

Kullback–Leibler divergence, Gaussian distribution, two-point method,
Pinsker, total variation distance
-/

namespace LTFP.MathlibExt.Probability

/-- The scalar **Gaussian two-point KL gap** as a function of the mean
separation `Δ = μ₀ - μ₁` and the common standard deviation `σ`:

`gaussianKLScalar Δ σ = Δ² / (2 σ²)`.

This is the closed-form value of the Kullback–Leibler divergence
`KL(N(μ₀, σ²) ‖ N(μ₁, σ²))` between two univariate Gaussians with the
same variance and mean separation `Δ`. The fully measure-theoretic
form, evaluating `klDiv` on Mathlib's `gaussianReal` measures, is
deferred to a future PR; the present definition isolates the scalar
value so that downstream consumers (Pinsker, Le Cam two-point method)
can compose against it. -/
noncomputable def gaussianKLScalar (Δ σ : ℝ) : ℝ := Δ ^ 2 / (2 * σ ^ 2)

/-- Nonnegativity of the Gaussian two-point KL gap. Holds whenever the
common standard deviation is strictly positive, regardless of the sign
of the mean separation `Δ`. -/
theorem gaussianKLScalar_nonneg
    {Δ σ : ℝ} (hσ : 0 < σ) :
    0 ≤ gaussianKLScalar Δ σ := by
  unfold gaussianKLScalar
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  have h2σ2 : 0 < 2 * σ ^ 2 := by positivity
  exact div_nonneg hΔ2 h2σ2.le

/-- The Gaussian KL gap vanishes exactly when the mean separation is
zero. With `σ > 0`, the divergence `Δ² / (2σ²)` is zero iff `Δ = 0`. -/
theorem gaussianKLScalar_eq_zero_iff
    {Δ σ : ℝ} (hσ : 0 < σ) :
    gaussianKLScalar Δ σ = 0 ↔ Δ = 0 := by
  unfold gaussianKLScalar
  have h2σ2_ne : (2 * σ ^ 2 : ℝ) ≠ 0 := by positivity
  rw [div_eq_zero_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h₁ | h₂
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h₁
    · exact absurd h₂ h2σ2_ne
  · left; rw [h]; ring

/-- Monotonicity in `Δ²`: for fixed `σ > 0`, the Gaussian KL gap is a
nondecreasing function of `|Δ|` (equivalently of `Δ²`). Farther-apart
Gaussian means produce a larger KL divergence. -/
theorem gaussianKLScalar_mono_delta_sq
    {Δ₁ Δ₂ σ : ℝ} (hσ : 0 < σ) (h : Δ₁ ^ 2 ≤ Δ₂ ^ 2) :
    gaussianKLScalar Δ₁ σ ≤ gaussianKLScalar Δ₂ σ := by
  unfold gaussianKLScalar
  have h2σ2 : (0 : ℝ) < 2 * σ ^ 2 := by positivity
  exact div_le_div_of_nonneg_right h h2σ2.le

/-- Antitonicity in `σ²`: for fixed `Δ`, the Gaussian KL gap is a
nonincreasing function of the common variance `σ²`. Noisier
observations (larger `σ²`) shrink the KL divergence and make the two
hypotheses harder to distinguish. -/
theorem gaussianKLScalar_antitone_var
    {Δ σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (_hσ₂ : 0 < σ₂) (h : σ₁ ^ 2 ≤ σ₂ ^ 2) :
    gaussianKLScalar Δ σ₂ ≤ gaussianKLScalar Δ σ₁ := by
  unfold gaussianKLScalar
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  have h2σ1 : (0 : ℝ) < 2 * σ₁ ^ 2 := by positivity
  have h2 : (2 * σ₁ ^ 2 : ℝ) ≤ 2 * σ₂ ^ 2 := by linarith
  exact div_le_div_of_nonneg_left hΔ2 h2σ1 h2

/-- **Pinsker bound composed with the Gaussian KL value.**

Applying the Pinsker upper bound `pinskerBound x := √(x/2)` to the
Gaussian two-point KL value yields the classical testing-side bound

`pinskerBound (gaussianKLScalar Δ σ) = √( (Δ²/(2σ²)) / 2 ) = |Δ| / (2σ)`.

This is the standard form in which Pinsker's inequality is applied in
the Gaussian two-point method: `TV(N(μ₀, σ²), N(μ₁, σ²)) ≤ |Δ| / (2σ)`,
where `Δ = μ₀ - μ₁`. -/
theorem gaussianTwoPointPinskerBound
    {Δ σ : ℝ} (hσ : 0 < σ) :
    pinskerBound (gaussianKLScalar Δ σ) = |Δ| / (2 * σ) := by
  unfold pinskerBound gaussianKLScalar
  -- Rewrite the argument of `√` to `(|Δ| / (2σ))²`, then use `sqrt_sq`.
  have h2σ_pos : (0 : ℝ) < 2 * σ := by linarith
  have h2σ_nn : (0 : ℝ) ≤ 2 * σ := le_of_lt h2σ_pos
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have habs_nn : (0 : ℝ) ≤ |Δ| / (2 * σ) :=
    div_nonneg (abs_nonneg _) h2σ_nn
  have h_eq : Δ ^ 2 / (2 * σ ^ 2) / 2 = (|Δ| / (2 * σ)) ^ 2 := by
    have h_abs_sq : |Δ| ^ 2 = Δ ^ 2 := sq_abs Δ
    have h2σ_sq : (2 * σ) ^ 2 = 4 * σ ^ 2 := by ring
    rw [div_pow, h_abs_sq, h2σ_sq]
    field_simp
    ring
  rw [h_eq, Real.sqrt_sq habs_nn]

end LTFP.MathlibExt.Probability
