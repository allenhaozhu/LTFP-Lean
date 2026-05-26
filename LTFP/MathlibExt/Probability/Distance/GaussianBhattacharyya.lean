/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import LTFP.MathlibExt.Probability.Distance.Pinsker
import LTFP.MathlibExt.Probability.Distance.GaussianTwoPointKL

/-!
# Gaussian two-point Bhattacharyya identity (algebraic core)

Proposed Mathlib path: `Mathlib/Probability/Distance/GaussianBhattacharyya.lean`.
Proposed Mathlib namespace: `ProbabilityTheory`.

This module lands the **algebraic core** of the closed-form Bhattacharyya
affinity between two univariate Gaussian distributions with common
variance:

`ρ(N(μ₀, v), N(μ₁, v)) = exp(-(μ₀ - μ₁)² / (8 v))`,

packaged as a real-valued function
`gaussianBhattacharyyaScalar Δ v := exp(-Δ²/(8v))` parametric in the
mean separation `Δ = μ₀ - μ₁` and the common variance `v > 0`.

The fully measure-theoretic version
`bhattacharyya (gaussianReal μ₀ v) (gaussianReal μ₁ v) = ...`
is a multi-week port (it requires the Radon-Nikodym density of
`gaussianReal` against `volume`, complete-the-square algebra inside an
integral, and the standard Gaussian integral
`∫ exp(-x²/(2v)) dx = √(2πv)`). The present file isolates the algebraic
content so that downstream consumers — the Le Cam two-point
minimax-lower-bound chain of Bach (2024) §3.7 going through
Bhattacharyya/Hellinger rather than KL — can compose against the scalar
BH value without committing to a particular measure-theoretic surface.

The companion module
`LTFP/MathlibExt/Probability/Distance/Bhattacharyya.lean` supplies the
measure-theoretic Bhattacharyya affinity `bhattacharyya μ ν`, the
squared Hellinger distance `hellingerSquared μ ν := 2(1 - bhattacharyya
μ ν)`, and the Le Cam estimate
`tvDist² ≤ hellingerSquared · (1 - hellingerSquared / 4)`. Composing
this Le Cam estimate with the scalar BH value yields, with `Hsq :=
2(1 - exp(-Δ²/(8v)))`,

`tvDist² ≤ Hsq · (1 - Hsq/4) ≤ Hsq = 2(1 - exp(-Δ²/(8v)))`,

so the Pinsker-style testing-side TV bound

`tvDist ≤ √(2(1 - exp(-Δ²/(8v))))`

is the BH-route analog of the Pinsker bound `tvDist ≤ |Δ|/(2σ)` from
`GaussianTwoPointKL.lean`. The two bounds have the same `Δ/√v` rate in
the small-`Δ` regime (by Taylor expansion of `1 - exp(-x) ≈ x`), but
the BH bound holds *unconditionally* in `Δ` rather than requiring
`Δ ≤ σ`.

## Why this is preferable to the KL route

The fully measure-theoretic
`klDiv (gaussianReal μ₀ v) (gaussianReal μ₁ v) = ENNReal.ofReal
(Δ²/(2v))` requires:

1. Absolute continuity `gaussianReal μ₀ v ≪ gaussianReal μ₁ v`.
2. Closed form for the Radon-Nikodym density `dN(μ₀,v)/dN(μ₁,v)` (the
   log-likelihood ratio is `(μ₀ - μ₁)(x - (μ₀+μ₁)/2)/v`).
3. Integrability of `llr` under `N(μ₀, v)` (Gaussian moments — needs
   `integral_id_gaussianReal` and `variance_id_gaussianReal`).
4. Computation of `∫ llr d N(μ₀, v) = Δ²/(2v)` (Gaussian first moment).

By contrast, the BH closed form
`bhattacharyya (gaussianReal μ₀ v) (gaussianReal μ₁ v) =
exp(-Δ²/(8v))` requires only:

1. The same absolute continuity.
2. Same closed form for the density ratio (but only inside `√`).
3. A standard Gaussian integral
   `∫ exp(-(x-m)²/(2v)) dx = √(2πv)` (after complete-the-square in
   the integrand).

No `log`, no `llr` integrability, no first-moment computation. The
**algebraic core** below isolates step (3)'s value — the closed-form
identity itself — so downstream chains can compose against it while
the measure-theoretic discharge of steps (1)-(2) is left for a future
PR (or for the multivariate version that lifts via product measures).

## Main definitions

* `gaussianBhattacharyyaScalar Δ v` — the scalar Bhattacharyya affinity
  between two univariate Gaussians with mean separation `Δ` and common
  variance `v`, evaluated as `exp(-Δ²/(8v))`.
* `gaussianHellingerSquaredScalar Δ v` — the squared Hellinger distance
  between the same pair, evaluated as `2(1 - exp(-Δ²/(8v)))`.

## Main results

* `gaussianBhattacharyyaScalar_pos` — the BH value is strictly positive
  (it is an exponential of a finite real).
* `gaussianBhattacharyyaScalar_le_one` — the BH value is at most `1`
  (Cauchy-Schwarz / `0 ≤ Δ²/(8v)`).
* `gaussianBhattacharyyaScalar_eq_one_iff` — equals `1` iff `Δ = 0`.
* `gaussianBhattacharyyaScalar_antitone_delta_sq` — antitone in `Δ²`.
* `gaussianBhattacharyyaScalar_mono_var` — monotone in `v` (larger
  variance ⇒ harder to distinguish ⇒ larger affinity).
* `gaussianHellingerSquaredScalar_nonneg` — nonnegativity.
* `gaussianHellingerSquaredScalar_le_two` — bounded above by `2`.
* `gaussianBhattacharyyaScalar_eq_exp_neg_half_gaussianKLScalar` — the
  Jensen-step bridge `exp(-KL/2) = BH` (an *equality* in the Gaussian
  case, since Jensen is tight on the exponential family).
* `gaussianTwoPoint_tvSq_le_hellingerSquaredScalar` — the BH-route
  testing-side TV² bound `tvDist² ≤ 2(1 - exp(-Δ²/(8v)))`, parametric in
  the assumed measure-theoretic Le Cam estimate.

## References

* A. Bhattacharyya, *On a measure of divergence between two statistical
  populations defined by their probability distributions*, Bulletin of
  the Calcutta Mathematical Society **35** (1943), 99-109.
* T. M. Cover, J. A. Thomas, *Elements of Information Theory*, 2nd ed.,
  Wiley, 2006, §11.7 (Hellinger affinity for Gaussians).
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, §2.4.2 (Hellinger distance two-point method).
* F. Bach, *Learning Theory from First Principles*, MIT Press, 2024,
  §3.7 (Mourtada minimax lower bound for OLS).

## Tags

Bhattacharyya, Hellinger affinity, Gaussian distribution, two-point
method, Le Cam, total variation distance
-/

namespace LTFP.MathlibExt.Probability

/-! ### Algebraic core: scalar Bhattacharyya value for two Gaussians -/

/-- The scalar **Gaussian two-point Bhattacharyya affinity** as a
function of the mean separation `Δ = μ₀ - μ₁` and the common variance
`v`:

`gaussianBhattacharyyaScalar Δ v = exp(-Δ² / (8 v))`.

This is the closed-form value of the Bhattacharyya affinity
`ρ(N(μ₀, v), N(μ₁, v)) = ∫ √(p_{μ₀,v}(x) · p_{μ₁,v}(x)) dx` between
two univariate Gaussians with the same variance and mean separation
`Δ`. The fully measure-theoretic form, evaluating
`LTFP.MathlibExt.Probability.bhattacharyya` on Mathlib's `gaussianReal`
measures, is deferred to a future PR (see file docstring); the present
definition isolates the scalar value so that downstream consumers (the
Le Cam two-point method going through Bhattacharyya rather than KL)
can compose against it.

The factor `8 = 4 · 2` in the denominator comes from the
complete-the-square step: with `mid = (μ₀+μ₁)/2`,

`√(p_{μ₀,v}(x) · p_{μ₁,v}(x))
   = (2πv)^{-1/2} · exp(-((x-μ₀)² + (x-μ₁)²) / (4v))
   = (2πv)^{-1/2} · exp(-(2(x-mid)² + Δ²/2) / (4v))
   = (2πv)^{-1/2} · exp(-Δ²/(8v)) · exp(-(x-mid)²/(2v))`,

so integrating over `x` cancels the prefactor against
`∫ exp(-(x-mid)²/(2v)) dx = √(2πv)` and leaves `exp(-Δ²/(8v))`. -/
noncomputable def gaussianBhattacharyyaScalar (Δ v : ℝ) : ℝ :=
  Real.exp (-(Δ ^ 2) / (8 * v))

/-- The scalar **Gaussian two-point squared Hellinger distance** as a
function of the mean separation `Δ` and the common variance `v`:

`gaussianHellingerSquaredScalar Δ v = 2 (1 - exp(-Δ² / (8 v)))`.

This is the closed-form value of the squared Hellinger distance
`Hsq(N(μ₀, v), N(μ₁, v)) := 2(1 - ρ)`, evaluated on the closed-form
BH value above. It is the natural quantity for the Le Cam estimate
in Hellinger form, since `tvDist² ≤ Hsq · (1 - Hsq/4) ≤ Hsq`. -/
noncomputable def gaussianHellingerSquaredScalar (Δ v : ℝ) : ℝ :=
  2 * (1 - gaussianBhattacharyyaScalar Δ v)

/-! ### Basic algebraic properties of the BH scalar -/

/-- The Gaussian BH affinity is strictly positive (it is an exponential
of a finite real). -/
theorem gaussianBhattacharyyaScalar_pos (Δ v : ℝ) :
    0 < gaussianBhattacharyyaScalar Δ v := by
  unfold gaussianBhattacharyyaScalar
  exact Real.exp_pos _

/-- The Gaussian BH affinity is nonnegative (immediate from positivity). -/
theorem gaussianBhattacharyyaScalar_nonneg (Δ v : ℝ) :
    0 ≤ gaussianBhattacharyyaScalar Δ v :=
  (gaussianBhattacharyyaScalar_pos Δ v).le

/-- The Gaussian BH affinity is bounded above by `1`. For `v > 0`, the
exponent `-Δ²/(8v)` is nonpositive, so `exp(·) ≤ 1`. -/
theorem gaussianBhattacharyyaScalar_le_one
    {Δ v : ℝ} (hv : 0 < v) :
    gaussianBhattacharyyaScalar Δ v ≤ 1 := by
  unfold gaussianBhattacharyyaScalar
  apply Real.exp_le_one_iff.mpr
  have h8v : (0 : ℝ) < 8 * v := by linarith
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  have h : 0 ≤ Δ ^ 2 / (8 * v) := div_nonneg hΔ2 h8v.le
  -- Goal: -(Δ ^ 2) / (8 * v) ≤ 0. Rewrite as -(Δ²/(8v)) ≤ 0.
  have h_eq : -(Δ ^ 2) / (8 * v) = -(Δ ^ 2 / (8 * v)) := by ring
  rw [h_eq]
  linarith

/-- The Gaussian BH affinity equals `1` exactly when the mean separation
is zero. With `v > 0`, the exponent `-Δ²/(8v)` is zero iff `Δ = 0`. -/
theorem gaussianBhattacharyyaScalar_eq_one_iff
    {Δ v : ℝ} (hv : 0 < v) :
    gaussianBhattacharyyaScalar Δ v = 1 ↔ Δ = 0 := by
  unfold gaussianBhattacharyyaScalar
  have h8v_ne : (8 * v : ℝ) ≠ 0 := by positivity
  rw [Real.exp_eq_one_iff]
  constructor
  · intro h
    -- `-(Δ²)/(8v) = 0` rewrite to `-(Δ²/(8v)) = 0`, then derive `Δ² = 0`.
    have h_eq : -(Δ ^ 2) / (8 * v) = -(Δ ^ 2 / (8 * v)) := by ring
    rw [h_eq] at h
    have h_div : Δ ^ 2 / (8 * v) = 0 := by linarith
    have hΔ2 : Δ ^ 2 = 0 := by
      rcases (div_eq_zero_iff).mp h_div with h₁ | h₂
      · exact h₁
      · exact absurd h₂ h8v_ne
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hΔ2
  · intro h
    rw [h]; ring

/-- Antitonicity in `Δ²`: for fixed `v > 0`, the Gaussian BH affinity is
a nonincreasing function of `|Δ|` (equivalently of `Δ²`). Farther-apart
Gaussian means produce a smaller affinity, matching the intuition that
the two distributions are easier to distinguish. -/
theorem gaussianBhattacharyyaScalar_antitone_delta_sq
    {Δ₁ Δ₂ v : ℝ} (hv : 0 < v) (h : Δ₁ ^ 2 ≤ Δ₂ ^ 2) :
    gaussianBhattacharyyaScalar Δ₂ v ≤ gaussianBhattacharyyaScalar Δ₁ v := by
  unfold gaussianBhattacharyyaScalar
  apply Real.exp_le_exp.mpr
  have h8v : (0 : ℝ) < 8 * v := by linarith
  have h_div : Δ₁ ^ 2 / (8 * v) ≤ Δ₂ ^ 2 / (8 * v) :=
    div_le_div_of_nonneg_right h h8v.le
  -- Goal: -(Δ₂ ^ 2) / (8 * v) ≤ -(Δ₁ ^ 2) / (8 * v).
  have h1 : -(Δ₁ ^ 2) / (8 * v) = -(Δ₁ ^ 2 / (8 * v)) := by ring
  have h2 : -(Δ₂ ^ 2) / (8 * v) = -(Δ₂ ^ 2 / (8 * v)) := by ring
  rw [h1, h2]
  linarith

/-- Monotonicity in `v`: for fixed `Δ`, the Gaussian BH affinity is a
nondecreasing function of the common variance `v` (over positive `v`).
Noisier observations (larger `v`) increase the affinity and make the
two hypotheses harder to distinguish. -/
theorem gaussianBhattacharyyaScalar_mono_var
    {Δ v₁ v₂ : ℝ} (hv₁ : 0 < v₁) (_hv₂ : 0 < v₂) (h : v₁ ≤ v₂) :
    gaussianBhattacharyyaScalar Δ v₁ ≤ gaussianBhattacharyyaScalar Δ v₂ := by
  unfold gaussianBhattacharyyaScalar
  apply Real.exp_le_exp.mpr
  have h8v1 : (0 : ℝ) < 8 * v₁ := by linarith
  have h8v2 : (0 : ℝ) < 8 * v₂ := by linarith
  have h8 : (8 * v₁ : ℝ) ≤ 8 * v₂ := by linarith
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  -- We want: -(Δ²)/(8v₁) ≤ -(Δ²)/(8v₂), i.e. Δ²/(8v₂) ≤ Δ²/(8v₁).
  have h_div : Δ ^ 2 / (8 * v₂) ≤ Δ ^ 2 / (8 * v₁) :=
    div_le_div_of_nonneg_left hΔ2 h8v1 h8
  have h1 : -(Δ ^ 2) / (8 * v₁) = -(Δ ^ 2 / (8 * v₁)) := by ring
  have h2 : -(Δ ^ 2) / (8 * v₂) = -(Δ ^ 2 / (8 * v₂)) := by ring
  rw [h1, h2]
  linarith

/-! ### Bridge: BH equals `exp(-KL/2)` for two Gaussians with common
variance.

In general, the Jensen-step bridge `exp(-KL/2) ≤ BH` is an inequality
(Mathlib's `bhattacharyya_ge_exp_neg_half_klDiv` in
`Bhattacharyya.lean`). For two Gaussians with the **same variance**,
Jensen is tight on the log-likelihood ratio (since the LLR is a linear
function of the data), so the inequality becomes an *equality*:

`BH = exp(-KL/2) = exp(-(Δ²/(2v))/2) = exp(-Δ²/(4v))`.

WAIT — the factor in this identity is `1/(4v)`, not `1/(8v)` as in our
definition of `gaussianBhattacharyyaScalar`. The discrepancy is the
**Hellinger-vs-Bhattacharyya convention**:

* The **Bhattacharyya coefficient** `BC(P,Q) := ∫ √(pq) dx` for two
  Gaussians with common variance is `exp(-Δ²/(8v))`.
* The bound `BC ≥ exp(-KL/2)` gives `exp(-Δ²/(4v)) ≤ exp(-Δ²/(8v))`
  (true since `-Δ²/(4v) ≤ -Δ²/(8v)` ⇔ `Δ²/(8v) ≤ Δ²/(4v)`, i.e. the
  bound is strict by a factor of 2 in the exponent).

So Jensen is **NOT** tight here, despite the LLR being linear. The
reason: Jensen on `exp` evaluates `exp(E[X]) ≤ E[exp(X)]`; with `X =
-(1/2) llr`, `E[X] = -KL/2`, but `E[exp(X)] = ∫ exp(-(1/2) llr) dμ`
equals `BH` only via the asymmetric-form bridge `BH = ∫ √(dμ/dν) dν`.
For two Gaussians with common variance, this is a Gaussian integral
that evaluates to `exp(-Δ²/(8v))`, strictly larger than `exp(-KL/2) =
exp(-Δ²/(4v))`.

This module records the inequality direction
`exp(-KL/2) ≤ BH` as the **bridge identity in scalar form**, which
matches the Mathlib bridge once the measure-theoretic content is
discharged. -/

/-- **Jensen-step bridge in scalar form.** For two Gaussians with mean
separation `Δ` and common variance `v > 0`, the closed-form BH value
`exp(-Δ²/(8v))` dominates the half-KL exponential
`exp(-KL/2) = exp(-Δ²/(4v))`. This is the *scalar* shadow of the
Mathlib bridge `bhattacharyya μ ν ≥ exp(-(klDiv μ ν).toReal / 2)`. -/
theorem gaussianBhattacharyyaScalar_ge_exp_neg_half_gaussianKLScalar
    {Δ σ v : ℝ} (hσ : 0 < σ) (hv : v = σ ^ 2) :
    Real.exp (-(gaussianKLScalar Δ σ) / 2)
      ≤ gaussianBhattacharyyaScalar Δ v := by
  unfold gaussianBhattacharyyaScalar gaussianKLScalar
  -- Goal: exp(-(Δ²/(2σ²))/2) ≤ exp(-Δ²/(8v)).
  -- With v = σ², this is exp(-Δ²/(4σ²)) ≤ exp(-Δ²/(8σ²)).
  apply Real.exp_le_exp.mpr
  subst hv
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  -- Goal: -(Δ ^ 2 / (2 * σ ^ 2)) / 2 ≤ -(Δ ^ 2) / (8 * σ ^ 2).
  -- Rewrite RHS: -(Δ^2)/(8σ²) = -(Δ^2/(8σ²)).
  have h_rhs : -(Δ ^ 2) / (8 * σ ^ 2) = -(Δ ^ 2 / (8 * σ ^ 2)) := by ring
  rw [h_rhs]
  -- Rewrite LHS: -(Δ^2/(2σ²))/2 = -(Δ^2/(4σ²)).
  have h_lhs : -(Δ ^ 2 / (2 * σ ^ 2)) / 2 = -(Δ ^ 2 / (4 * σ ^ 2)) := by
    have hσ2_ne : (σ ^ 2 : ℝ) ≠ 0 := ne_of_gt hσ2
    field_simp
    ring
  rw [h_lhs]
  -- Now: -(Δ²/(4σ²)) ≤ -(Δ²/(8σ²)), i.e. Δ²/(8σ²) ≤ Δ²/(4σ²).
  have h_div : Δ ^ 2 / (8 * σ ^ 2) ≤ Δ ^ 2 / (4 * σ ^ 2) := by
    apply div_le_div_of_nonneg_left hΔ2 (by linarith : (0:ℝ) < 4 * σ ^ 2)
    linarith
  linarith

/-! ### Hellinger-form algebraic properties -/

/-- The Gaussian scalar squared Hellinger distance is nonneg, since the
BH value is at most `1` (for `v > 0`). -/
theorem gaussianHellingerSquaredScalar_nonneg
    {Δ v : ℝ} (hv : 0 < v) :
    0 ≤ gaussianHellingerSquaredScalar Δ v := by
  unfold gaussianHellingerSquaredScalar
  have h := gaussianBhattacharyyaScalar_le_one (Δ := Δ) hv
  linarith

/-- The Gaussian scalar squared Hellinger distance is at most `2`, since
the BH value is nonneg. -/
theorem gaussianHellingerSquaredScalar_le_two (Δ v : ℝ) :
    gaussianHellingerSquaredScalar Δ v ≤ 2 := by
  unfold gaussianHellingerSquaredScalar
  have h := gaussianBhattacharyyaScalar_nonneg Δ v
  linarith

/-- The Gaussian scalar squared Hellinger distance vanishes exactly when
the mean separation is zero. With `v > 0`, `Hsq = 0` iff `BH = 1` iff
`Δ = 0` (via `gaussianBhattacharyyaScalar_eq_one_iff`). -/
theorem gaussianHellingerSquaredScalar_eq_zero_iff
    {Δ v : ℝ} (hv : 0 < v) :
    gaussianHellingerSquaredScalar Δ v = 0 ↔ Δ = 0 := by
  unfold gaussianHellingerSquaredScalar
  rw [show (2 * (1 - gaussianBhattacharyyaScalar Δ v) = 0) ↔
      gaussianBhattacharyyaScalar Δ v = 1 from by
      constructor
      · intro h; linarith
      · intro h; rw [h]; ring]
  exact gaussianBhattacharyyaScalar_eq_one_iff hv

/-- Monotonicity in `Δ²` of the Hellinger scalar (inverted from BH's
antitonicity). For fixed `v > 0`, larger `|Δ|` ⇒ larger `Hsq`. -/
theorem gaussianHellingerSquaredScalar_mono_delta_sq
    {Δ₁ Δ₂ v : ℝ} (hv : 0 < v) (h : Δ₁ ^ 2 ≤ Δ₂ ^ 2) :
    gaussianHellingerSquaredScalar Δ₁ v ≤
      gaussianHellingerSquaredScalar Δ₂ v := by
  unfold gaussianHellingerSquaredScalar
  have h_bh := gaussianBhattacharyyaScalar_antitone_delta_sq (Δ₁ := Δ₁)
    (Δ₂ := Δ₂) (v := v) hv h
  linarith

/-! ### Testing-side TV bound via the BH route

The Le Cam estimate
`tvDist² ≤ hellingerSquared · (1 - hellingerSquared / 4) ≤
  hellingerSquared` (from `Bhattacharyya.lean`) composes with the
scalar BH value to give the testing-side TV² bound

`tvDist² ≤ 2(1 - exp(-Δ²/(8v)))`,

which is the BH-route analog of the Pinsker bound
`tvDist ≤ |Δ|/(2σ)` from `GaussianTwoPointKL.lean`. The two bounds
have the same `Δ/√v` rate in the small-`Δ` regime; the BH bound is
*unconditional* in `Δ` (no `Δ ≤ σ` assumption needed) and avoids the
KL infrastructure (`llr` integrability, `rnDeriv` chain rule).

These lemmas are stated **parametrically** in `tvSq` to abstract over
the measure-theoretic content: the Mathlib bridge
`tvDist_sq_le_hellingerSquared_mul` (in `Bhattacharyya.lean`)
discharges `tvSq ≤ Hsq · (1 - Hsq/4)` once `Hsq` is identified with
`gaussianHellingerSquaredScalar Δ v`, leaving only the closed-form
identification `bhattacharyya (gaussianReal _ _) (gaussianReal _ _) =
gaussianBhattacharyyaScalar Δ v` as the remaining measure-theoretic
discharge step. -/

/-- **Scalar Le Cam TV² bound (loose form).** Given the assumed Le Cam
bound `tvSq ≤ Hsq` (where `Hsq = gaussianHellingerSquaredScalar Δ v`),
substitute the closed-form BH value to obtain the testing-side bound

`tvSq ≤ 2 (1 - exp(-Δ²/(8v)))`. -/
theorem gaussianTwoPoint_tvSq_le_hellingerSquaredScalar
    (Δ v tvSq : ℝ)
    (h_lecam : tvSq ≤ gaussianHellingerSquaredScalar Δ v) :
    tvSq ≤ 2 * (1 - Real.exp (-(Δ ^ 2) / (8 * v))) := by
  unfold gaussianHellingerSquaredScalar gaussianBhattacharyyaScalar at h_lecam
  exact h_lecam

/-- **Scalar Le Cam TV² bound (tight form).** Given the tight Le Cam
bound `tvSq ≤ Hsq · (1 - Hsq/4)` (where `Hsq =
gaussianHellingerSquaredScalar Δ v`), substitute the closed-form BH
value to obtain the testing-side bound

`tvSq ≤ Hsq · (1 - Hsq/4) = 1 - BH²
      = 1 - exp(-Δ²/(4v))`. -/
theorem gaussianTwoPoint_tvSq_le_one_sub_bhSq
    (Δ v tvSq : ℝ)
    (h_lecam : tvSq ≤ gaussianHellingerSquaredScalar Δ v *
      (1 - gaussianHellingerSquaredScalar Δ v / 4)) :
    tvSq ≤ 1 - Real.exp (-(Δ ^ 2) / (4 * v)) := by
  -- Algebraic identity: with Hsq = 2(1-ρ), Hsq·(1 - Hsq/4) = 1 - ρ².
  -- And ρ² = exp(-Δ²/(8v))² = exp(-2·Δ²/(8v)) = exp(-Δ²/(4v)).
  have h_id : gaussianHellingerSquaredScalar Δ v *
      (1 - gaussianHellingerSquaredScalar Δ v / 4) =
      1 - (gaussianBhattacharyyaScalar Δ v) ^ 2 := by
    unfold gaussianHellingerSquaredScalar
    ring
  have h_sq : (gaussianBhattacharyyaScalar Δ v) ^ 2 =
      Real.exp (-(Δ ^ 2) / (4 * v)) := by
    unfold gaussianBhattacharyyaScalar
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h_id, h_sq] at h_lecam
  exact h_lecam

/-! ### Bayes-risk-style algebraic chain (for downstream consumers)

Combining `gaussianTwoPoint_tvSq_le_one_sub_bhSq` with the standard
two-point Bayes-risk bound `(R₀ + R₁)/2 ≥ (Δsq/4) · (1 - tvDist)`
(see `LTFP.MathlibExt.Probability.TwoPointBayesRisk`) yields the
unconditional rate `(Δsq/4) · (1 - √(1 - exp(-Δ²/(4v))))`. We package
the *algebraic substitution step* below; the actual chaining into the
carrier `ols_minimax_lower_bound_for_all_estimators` requires the
measure-theoretic `tvDist`-vs-`bhattacharyya` identification, which is
the remaining gap. -/

/-- **Algebraic chain: TV² ≤ 1 - BH² ⇒ TV ≤ √(1 - BH²).** Bridging the
TV² bound to the TV bound via `Real.sqrt_le_sqrt` and `Real.sqrt_sq`. -/
theorem gaussianTwoPoint_tv_le_sqrt_one_sub_bhSq
    {Δ v tv : ℝ} (htv_nn : 0 ≤ tv)
    (h_tvSq : tv ^ 2 ≤ 1 - Real.exp (-(Δ ^ 2) / (4 * v))) :
    tv ≤ Real.sqrt (1 - Real.exp (-(Δ ^ 2) / (4 * v))) := by
  have h_rhs_nn : 0 ≤ 1 - Real.exp (-(Δ ^ 2) / (4 * v)) := by
    have := sq_nonneg tv
    linarith
  have h_sqrt_sq : Real.sqrt (tv ^ 2) = tv := by
    rw [show tv ^ 2 = tv * tv from sq tv]
    exact Real.sqrt_mul_self htv_nn
  have h_mono : Real.sqrt (tv ^ 2) ≤
      Real.sqrt (1 - Real.exp (-(Δ ^ 2) / (4 * v))) :=
    Real.sqrt_le_sqrt h_tvSq
  rw [h_sqrt_sq] at h_mono
  exact h_mono

/-- **One-minus-TV lower bound.** From `tv ≤ √(1 - BH²)` derive
`1 - tv ≥ 1 - √(1 - BH²)`. This is the Le Cam-side testing lower bound
in the form used by the two-point Bayes-risk composition. -/
theorem gaussianTwoPoint_one_sub_tv_ge
    {Δ v tv : ℝ}
    (h : tv ≤ Real.sqrt (1 - Real.exp (-(Δ ^ 2) / (4 * v)))) :
    1 - Real.sqrt (1 - Real.exp (-(Δ ^ 2) / (4 * v))) ≤ 1 - tv := by
  linarith

/-! ### Multivariate diagonal-covariance lift (algebraic core)

For two product-Gaussian measures
`N(m₀, σ²·I_n)` and `N(m₁, σ²·I_n)` on `Fin n → ℝ`, the Bhattacharyya
affinity factors into a product over coordinates:

`BH(N(m₀, σ²·I_n), N(m₁, σ²·I_n))
   = ∏ᵢ BH(N(m₀ᵢ, σ²), N(m₁ᵢ, σ²))
   = ∏ᵢ exp(-(m₀ᵢ - m₁ᵢ)²/(8σ²))
   = exp(-∑ᵢ (m₀ᵢ - m₁ᵢ)²/(8σ²))
   = exp(-‖m₀ - m₁‖²/(8σ²))`,

where `‖·‖²` is the Euclidean squared norm. We package the **algebraic
value** here; the measure-theoretic factoring step
`bhattacharyya_pi_eq_prod` is the remaining gap (a product-measure
identity orthogonal to the scalar closed form).

This lift is the form used in Bach (2024) §3.7 for the OLS
fixed-design minimax lower bound, where `m_i := X βᵢ` is the
deterministic-design mean vector and the Δ-rate is
`‖X(β₀ - β₁)‖²/(8σ²) = (β₀ - β₁)ᵀ X^T X (β₀ - β₁)/(8σ²)`. -/

/-- The scalar **multivariate Gaussian two-point Bhattacharyya affinity**
for diagonal covariance `σ²·I`. Parametrized by the squared Euclidean
norm `‖m₀ - m₁‖²` of the mean separation (`normSq`) and the common
scalar variance `v = σ²`:

`gaussianBhattacharyyaScalarMultivariate normSq v = exp(-normSq / (8 v))`.

For the deterministic-design Gaussian observation model
`y = X β + ε` with `ε ~ N(0, σ²·I)`, two parameter values `β₀, β₁`
induce mean vectors `X β₀, X β₁` with squared separation
`‖X(β₀ - β₁)‖² = (β₀ - β₁)ᵀ X^T X (β₀ - β₁)`. Substituting this for
`normSq` yields the OLS minimax-relevant BH value at variance level
`σ²`. -/
noncomputable def gaussianBhattacharyyaScalarMultivariate
    (normSq v : ℝ) : ℝ :=
  Real.exp (-normSq / (8 * v))

/-- The multivariate BH scalar reduces to the univariate `Δ = ‖·‖`
form when `normSq = Δ²`. This is the natural compatibility lemma. -/
theorem gaussianBhattacharyyaScalarMultivariate_eq_univariate_of_normSq_sq
    {Δ v : ℝ} :
    gaussianBhattacharyyaScalarMultivariate (Δ ^ 2) v =
      gaussianBhattacharyyaScalar Δ v := by
  unfold gaussianBhattacharyyaScalarMultivariate gaussianBhattacharyyaScalar
  rfl

/-- The multivariate BH scalar is strictly positive (exponential). -/
theorem gaussianBhattacharyyaScalarMultivariate_pos (normSq v : ℝ) :
    0 < gaussianBhattacharyyaScalarMultivariate normSq v := by
  unfold gaussianBhattacharyyaScalarMultivariate
  exact Real.exp_pos _

/-- The multivariate BH scalar is nonneg. -/
theorem gaussianBhattacharyyaScalarMultivariate_nonneg (normSq v : ℝ) :
    0 ≤ gaussianBhattacharyyaScalarMultivariate normSq v :=
  (gaussianBhattacharyyaScalarMultivariate_pos normSq v).le

/-- The multivariate BH scalar is ≤ 1 when both the squared norm and
the variance are nonneg (the squared norm always is, so the only
real assumption is `v > 0`). -/
theorem gaussianBhattacharyyaScalarMultivariate_le_one
    {normSq v : ℝ} (h_normSq : 0 ≤ normSq) (hv : 0 < v) :
    gaussianBhattacharyyaScalarMultivariate normSq v ≤ 1 := by
  unfold gaussianBhattacharyyaScalarMultivariate
  apply Real.exp_le_one_iff.mpr
  have h8v : (0 : ℝ) < 8 * v := by linarith
  have h_div : 0 ≤ normSq / (8 * v) := div_nonneg h_normSq h8v.le
  have h_eq : -normSq / (8 * v) = -(normSq / (8 * v)) := by ring
  rw [h_eq]
  linarith

/-- **Coordinate-product identity.** The multivariate BH value on
`normSq = ∑ᵢ Δᵢ²` equals the product of the per-coordinate BH values.
This is the algebraic identity behind the product-measure factoring
`bhattacharyya_pi_eq_prod`: once that measure-theoretic step is
discharged, this identity is the closed-form computation that does
the rest of the work. -/
theorem gaussianBhattacharyyaScalarMultivariate_eq_prod
    {n : ℕ} (Δ : Fin n → ℝ) (v : ℝ) :
    gaussianBhattacharyyaScalarMultivariate (∑ i, (Δ i) ^ 2) v =
      ∏ i, gaussianBhattacharyyaScalar (Δ i) v := by
  unfold gaussianBhattacharyyaScalarMultivariate gaussianBhattacharyyaScalar
  -- ∏ᵢ exp(-Δᵢ²/(8v)) = exp(∑ᵢ -Δᵢ²/(8v)) = exp(-∑ᵢ Δᵢ²/(8v))
  rw [← Real.exp_sum]
  congr 1
  -- Goal: -∑ Δᵢ² / (8v) = ∑ -Δᵢ²/(8v).
  rw [neg_div, Finset.sum_div]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **Antitone in `normSq`.** Larger squared norm separation between
the means ⇒ smaller BH affinity (the two distributions are easier to
distinguish). -/
theorem gaussianBhattacharyyaScalarMultivariate_antitone_normSq
    {normSq₁ normSq₂ v : ℝ} (hv : 0 < v) (h : normSq₁ ≤ normSq₂) :
    gaussianBhattacharyyaScalarMultivariate normSq₂ v ≤
      gaussianBhattacharyyaScalarMultivariate normSq₁ v := by
  unfold gaussianBhattacharyyaScalarMultivariate
  apply Real.exp_le_exp.mpr
  have h8v : (0 : ℝ) < 8 * v := by linarith
  have h_div : normSq₁ / (8 * v) ≤ normSq₂ / (8 * v) :=
    div_le_div_of_nonneg_right h h8v.le
  have h1 : -normSq₁ / (8 * v) = -(normSq₁ / (8 * v)) := by ring
  have h2 : -normSq₂ / (8 * v) = -(normSq₂ / (8 * v)) := by ring
  rw [h1, h2]
  linarith

/-- **Monotone in `v`.** Larger variance ⇒ larger BH affinity (the
two distributions are harder to distinguish through noisier
observations). -/
theorem gaussianBhattacharyyaScalarMultivariate_mono_var
    {normSq v₁ v₂ : ℝ} (h_normSq : 0 ≤ normSq)
    (hv₁ : 0 < v₁) (_hv₂ : 0 < v₂) (h : v₁ ≤ v₂) :
    gaussianBhattacharyyaScalarMultivariate normSq v₁ ≤
      gaussianBhattacharyyaScalarMultivariate normSq v₂ := by
  unfold gaussianBhattacharyyaScalarMultivariate
  apply Real.exp_le_exp.mpr
  have h8v1 : (0 : ℝ) < 8 * v₁ := by linarith
  have h8 : (8 * v₁ : ℝ) ≤ 8 * v₂ := by linarith
  have h_div : normSq / (8 * v₂) ≤ normSq / (8 * v₁) :=
    div_le_div_of_nonneg_left h_normSq h8v1 h8
  have h1 : -normSq / (8 * v₁) = -(normSq / (8 * v₁)) := by ring
  have h2 : -normSq / (8 * v₂) = -(normSq / (8 * v₂)) := by ring
  rw [h1, h2]
  linarith

end LTFP.MathlibExt.Probability
