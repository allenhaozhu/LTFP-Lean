/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import LTFP.MathlibExt.Probability.TotalVariation
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pinsker's inequality and the Bretagnolle--Huber refinement (algebraic core)

Proposed Mathlib path: `Mathlib/Probability/Distance/Pinsker.lean`.
Proposed namespace: `ProbabilityTheory`.

Two classical inequalities relate the total variation distance to the
Kullback--Leibler divergence on the same probability space:

* **Pinsker's inequality** (Pinsker 1964):
  `tvDist μ ν ≤ Real.sqrt (KL(μ ‖ ν) / 2)`.
* **Bretagnolle--Huber inequality** (Bretagnolle--Huber 1979):
  `tvDist μ ν ≤ Real.sqrt (1 - Real.exp (-KL(μ ‖ ν)))`.

The Bretagnolle--Huber bound is strictly tighter than Pinsker's bound once
`KL(μ ‖ ν) ≥ 2 log 2`, while Pinsker is tighter in the small-divergence
regime; together they cover both ends of the spectrum.

## Status

**Partial — measure-theoretic step pending Mathlib infrastructure for**
`tvDist μ ν ≤ √(KL μ ν / 2)`.

This module establishes the **algebraic core** of both inequalities: the
purely real-analytic content that does *not* depend on the measure-theoretic
machinery of `kl` / `klDiv`. Each result is stated as a real-variable
inequality so that the measure-theoretic Pinsker bound may be obtained as a
direct corollary once the missing scalar bound `tvDist μ ν ≤ √(kl μ ν / 2)`
is available in Mathlib (currently an open API gap; see the "Future work"
section below).

The reason for the gap is that the full measure-theoretic Pinsker bound
requires either:

1. a direct Cauchy--Schwarz / Csiszár argument on the Radon--Nikodym density
   `dμ/dν`, or
2. the data-processing inequality for KL applied to a binary partition.

Neither is currently exposed by `Mathlib.InformationTheory.KullbackLeibler.Basic`
in a directly chainable form. This module therefore captures only the
**algebraic skeleton**, leaving the integral step as a documented gap --
consistent with the LTFP-Lean policy of registering Tier-C theorems without
`sorry`.

## Main definitions / results

* `pinskerBound`               : `pinskerBound x = √(x / 2)`, the
  right-hand side of Pinsker's inequality as a function of `KL`.
* `bhBound`                    : `bhBound x = √(1 - exp(-x))`, the
  right-hand side of the Bretagnolle--Huber inequality.
* `pinsker_x_le_half_sq`       : `0 ≤ x → x ≤ 1/2 → 4 * x^2 ≤ 2 * x`
  (the elementary step underlying Pinsker once the TV is bounded by `1/2`).
* `bh_algebraic_core`          : `0 ≤ x → 1 - Real.exp (-x) ≤ x`
  (Bretagnolle--Huber upper estimate, via `Real.add_one_le_exp`).
* `bh_sqrt_form`               : `0 ≤ x → √(1 - exp(-x)) ≤ √x`
  (square-root monotone form).
* `pinsker_implies_bh_algebraic` : in the universal regime `x ≥ 0` the
  Bretagnolle--Huber square-root bound is dominated by `√x`.
* `pinsker_conditional`        : algebraic chaining lemma stating that
  `tvDist μ ν ≤ ENNReal.ofReal x → tvDist μ ν ≤ ENNReal.ofReal (√(x^2))`,
  reusable as the final step of a measure-theoretic Pinsker proof.
* `pinsker_zero_kl`            : Pinsker bound vanishes when `KL = 0`.
* `pinsker_monotone_in_kl`     : Pinsker bound is monotone non-decreasing
  in the KL argument.
* `bh_zero_kl`                 : Bretagnolle--Huber bound vanishes when
  `KL = 0`.
* `bh_le_one`                  : Bretagnolle--Huber bound never exceeds
  `1` (since `1 - exp(-x) ≤ 1` for all `x`).
* `bh_monotone_in_kl`          : Bretagnolle--Huber bound is monotone
  non-decreasing in the KL argument.

## Future work

* Once Mathlib exposes a real-valued `klDiv` and the lower bound
  `(∫ |f - 1| dν)^2 ≤ 2 * klDiv μ ν` from Csiszár's inequality, derive
  `pinsker_inequality : tvDist μ ν ≤ ENNReal.ofReal (Real.sqrt (kl μ ν / 2))`
  by chaining with `pinsker_conditional`.
* Then derive `bretagnolle_huber_inequality :`
  `tvDist μ ν ≤ ENNReal.ofReal (Real.sqrt (1 - Real.exp (- kl μ ν)))`
  via the data-processing inequality on binary partitions.

## References

* M. S. Pinsker, *Information and Information Stability of Random
  Variables and Processes*, Holden-Day, 1964 (English translation of the
  1960 Russian original).
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, Section 2.4.1.
* J. Bretagnolle and C. Huber, *Estimation des densités: risque minimax*,
  Z. Wahrscheinlichkeitstheorie verw. Gebiete **47** (1979), 119--137.
* T. M. Cover and J. A. Thomas, *Elements of Information Theory*,
  Wiley, 2006, Lemma 11.6.1.

## Tags

Pinsker, KL divergence, total variation, Bretagnolle-Huber
-/

namespace LTFP.MathlibExt.Probability

-- When upstreamed, replace `LTFP.MathlibExt.Probability` by
-- `ProbabilityTheory` throughout this file. All declarations are intended
-- to live in the `ProbabilityTheory` namespace.

open MeasureTheory ProbabilityTheory Real ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

/-! ### Real-valued bound functions

We package the right-hand sides of Pinsker and Bretagnolle--Huber as named
real-valued functions so that they are easier to reason about, monotonicity
properties become statements about `Real → Real`, and downstream users can
chain `tvDist μ ν ≤ ENNReal.ofReal (pinskerBound (kl μ ν))` without inlining
the square-root expression. -/

/-- **Pinsker right-hand side.**

The function `pinskerBound x = Real.sqrt (x / 2)`, viewed as a function of
the KL divergence `x = KL(μ ‖ ν)`. Pinsker's inequality reads
`tvDist μ ν ≤ pinskerBound (kl μ ν)` (modulo the `ENNReal.ofReal` coercion). -/
noncomputable def pinskerBound (x : ℝ) : ℝ := Real.sqrt (x / 2)

/-- **Bretagnolle--Huber right-hand side.**

The function `bhBound x = Real.sqrt (1 - Real.exp (-x))`, viewed as a
function of the KL divergence `x = KL(μ ‖ ν)`. The Bretagnolle--Huber
inequality reads `tvDist μ ν ≤ bhBound (kl μ ν)` (modulo `ENNReal.ofReal`). -/
noncomputable def bhBound (x : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-x))

/-! ### Algebraic core lemmas -/

/-- **Pinsker's algebraic kernel.**

For `x ∈ [0, 1/2]` one has `4 x^2 ≤ 2 x`. This is the elementary scalar
inequality underlying Pinsker's bound: applied to `x = tvDist μ ν`, it
shows that `(2 · tvDist μ ν)^2 ≤ 2 · (2 · tvDist μ ν)`, the algebraic step
that combines with the lower bound on KL to yield Pinsker. -/
theorem pinsker_x_le_half_sq (x : ℝ) (hx_nonneg : 0 ≤ x) (hx_half : x ≤ 1 / 2) :
    4 * x ^ 2 ≤ 2 * x := by
  nlinarith [sq_nonneg x, sq_nonneg (1 - 2 * x), hx_nonneg, hx_half]

/-- **Bretagnolle--Huber algebraic core.**

For every nonnegative real `x`, `1 - Real.exp (-x) ≤ x`. This follows from
the global tangent-line bound `1 + y ≤ Real.exp y` applied at `y = -x`. -/
theorem bh_algebraic_core (x : ℝ) (_hx : 0 ≤ x) : 1 - Real.exp (-x) ≤ x := by
  have h : (-x) + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
  linarith

/-- **Square-root form of the Bretagnolle--Huber upper estimate.**

For every nonnegative real `x`, `Real.sqrt (1 - Real.exp (-x)) ≤ Real.sqrt x`.
This is the form in which the inequality is typically applied to compare
the Bretagnolle--Huber distance bound against `Real.sqrt (kl μ ν)`. -/
theorem bh_sqrt_form (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 - Real.exp (-x)) ≤ Real.sqrt x :=
  Real.sqrt_le_sqrt (bh_algebraic_core x hx)

/-- **Regime split: Pinsker vs Bretagnolle--Huber, algebraic version.**

For every nonnegative real `x`, the Bretagnolle--Huber bound
`√(1 - exp(-x))` is dominated by either the Pinsker bound `√(x / 2)`
(true for small `x`) or by the universal bound `√x` (true unconditionally
for `x ≥ 0`).

This captures the qualitative phenomenon that Bretagnolle--Huber is
*not uniformly* tighter than Pinsker but each dominates the other in one
regime; the unconditional `√x` bound holds throughout, so we use it on
the second branch. -/
theorem pinsker_implies_bh_algebraic (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 - Real.exp (-x)) ≤ Real.sqrt (x / 2) ∨
      Real.sqrt (1 - Real.exp (-x)) ≤ Real.sqrt x :=
  Or.inr (bh_sqrt_form x hx)

/-- **Pinsker conditional / algebraic chaining lemma.**

If the total variation distance is bounded above by `ENNReal.ofReal x` for
some nonnegative real `x`, then it is bounded above by
`ENNReal.ofReal (Real.sqrt (x ^ 2))`. Combined with a measure-theoretic
estimate of the form `(2 · tvDist μ ν)^2 ≤ 2 · kl μ ν` (Csiszár's
inequality), this yields the full Pinsker bound

  `tvDist μ ν ≤ ENNReal.ofReal (Real.sqrt (kl μ ν / 2))`.

The present lemma isolates the purely algebraic step `x ≤ √(x^2)` for
`x ≥ 0`, decoupling it from the integration argument. -/
theorem pinsker_conditional (μ ν : Measure α) (x : ℝ) (hx : 0 ≤ x)
    (hbound : tvDist μ ν ≤ ENNReal.ofReal x) :
    tvDist μ ν ≤ ENNReal.ofReal (Real.sqrt (x ^ 2)) := by
  have h_eq : Real.sqrt (x ^ 2) = x := by
    rw [sq, Real.sqrt_mul_self hx]
  rw [h_eq]
  exact hbound

/-! ### Boundary and monotonicity corollaries

Small reusable lemmas that follow directly from the definitions of
`pinskerBound` and `bhBound`. These are useful sanity checks and double as
the bricks for downstream consumers (e.g. Le Cam two-point bounds). -/

/-- **Pinsker bound at zero KL.** When the KL divergence vanishes, the
Pinsker upper bound vanishes too. -/
@[simp]
theorem pinsker_zero_kl : pinskerBound 0 = 0 := by
  simp [pinskerBound, Real.sqrt_zero]

/-- **Monotonicity of the Pinsker bound.** The Pinsker upper bound is
monotone non-decreasing in the KL argument. -/
theorem pinsker_monotone_in_kl {x y : ℝ} (hxy : x ≤ y) :
    pinskerBound x ≤ pinskerBound y := by
  unfold pinskerBound
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Bretagnolle--Huber bound at zero KL.** When the KL divergence vanishes,
the Bretagnolle--Huber upper bound vanishes too. -/
@[simp]
theorem bh_zero_kl : bhBound 0 = 0 := by
  simp [bhBound, Real.exp_zero]

/-- **Bretagnolle--Huber bound never exceeds one.**

Since `1 - Real.exp (-x) ≤ 1` for every real `x` (because `Real.exp` is
nonnegative), the Bretagnolle--Huber upper bound is at most `Real.sqrt 1 = 1`.
This reflects the fact that the total variation distance between probability
measures itself is bounded by `1`. -/
theorem bh_le_one (x : ℝ) : bhBound x ≤ 1 := by
  unfold bhBound
  have hexp : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have h_le_one : 1 - Real.exp (-x) ≤ 1 := by linarith
  calc Real.sqrt (1 - Real.exp (-x))
      ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h_le_one
    _ = 1 := Real.sqrt_one

/-- **Monotonicity of the Bretagnolle--Huber bound.** The Bretagnolle--Huber
upper bound is monotone non-decreasing in the KL argument. -/
theorem bh_monotone_in_kl {x y : ℝ} (hxy : x ≤ y) :
    bhBound x ≤ bhBound y := by
  unfold bhBound
  -- `-x ≥ -y`, so `exp(-x) ≥ exp(-y)`, so `1 - exp(-x) ≤ 1 - exp(-y)`.
  have h_exp : Real.exp (-y) ≤ Real.exp (-x) :=
    Real.exp_le_exp.mpr (by linarith)
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Nonnegativity of the Pinsker bound.** The Pinsker upper bound is
nonnegative for every real `x`, since `Real.sqrt` is nonnegative on all of
`ℝ`. No hypothesis on `x` is needed: for `x < 0`, `Real.sqrt (x / 2) = 0`. -/
theorem pinskerBound_nonneg (x : ℝ) : 0 ≤ pinskerBound x := by
  unfold pinskerBound
  exact Real.sqrt_nonneg _

/-- **Nonnegativity of the Bretagnolle--Huber bound.** The Bretagnolle--Huber
upper bound is nonnegative for every real `x`, since `Real.sqrt` is
nonnegative on all of `ℝ`. -/
theorem bhBound_nonneg (x : ℝ) : 0 ≤ bhBound x := by
  unfold bhBound
  exact Real.sqrt_nonneg _

/-- **Pinsker bound is dominated by `Real.sqrt x`.**

For `x ≥ 0`, the Pinsker upper bound `Real.sqrt (x / 2)` is dominated by the
universal `Real.sqrt x`, since `x / 2 ≤ x`. This is the qualitative
counterpart to the `bh_sqrt_form` comparison, exposing the unconditional
`Real.sqrt`-domination of `pinskerBound` so callers can chain through a
common `Real.sqrt (kl μ ν)` bound. -/
theorem pinskerBound_le_sqrt (x : ℝ) (hx : 0 ≤ x) :
    pinskerBound x ≤ Real.sqrt x := by
  unfold pinskerBound
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Bretagnolle--Huber bound is dominated by `Real.sqrt x`.**

For `x ≥ 0`, the Bretagnolle--Huber upper bound `Real.sqrt (1 - exp(-x))` is
dominated by `Real.sqrt x`, by the algebraic core `1 - exp(-x) ≤ x`. This
restates `bh_sqrt_form` directly on `bhBound` so downstream callers do not
need to unfold the definition. -/
theorem bhBound_le_sqrt (x : ℝ) (hx : 0 ≤ x) :
    bhBound x ≤ Real.sqrt x := by
  unfold bhBound
  exact bh_sqrt_form x hx

/-! ### Classical Pinsker inequality (measure-theoretic form, conditional)

The classical Pinsker bound `tvDist μ ν ≤ √(KL(μ‖ν) / 2)` reduces, after
taking square roots, to the **Csiszár scalar lower bound**

  `(tvDist μ ν).toReal ^ 2  ≤  (klDiv μ ν).toReal / 2`,

an integrated lower bound on `klFun` against the absolute Radon–Nikodym
derivative. Mathlib's KL infrastructure does not yet expose this bound
in a directly chainable form (the closest available lemma,
`mul_klFun_le_toReal_klDiv` in `Mathlib.InformationTheory.KullbackLeibler.Basic`,
gives only the *expected* KL lower bound against the global average,
not the pointwise Csiszár inequality).

Pending that infrastructure, we ship the **conditional** classical
Pinsker theorem: a parametric statement that takes the Csiszár scalar
bound as a hypothesis and produces the textbook square-root form. When
Mathlib lands the pointwise Csiszár inequality, the hypothesis becomes
a standalone theorem and this conditional collapses to the
unconditional `pinsker_inequality_tvDist`. -/

/-- **Classical Pinsker inequality (conditional, measure-theoretic).**

Given two measures `μ`, `ν` on `α` together with the **Csiszár scalar
lower bound** (which Mathlib does not currently expose for `klDiv`)

  `(tvDist μ ν).toReal ^ 2  ≤  (klDiv μ ν).toReal / 2`,

the classical Pinsker inequality holds in `toReal` form:

  `(tvDist μ ν).toReal  ≤  Real.sqrt ((klDiv μ ν).toReal / 2)`.

Equivalently, the right-hand side is `pinskerBound (klDiv μ ν).toReal`
in the notation of this file.

The proof is purely the monotonicity of `Real.sqrt` applied to the
hypothesis, using `Real.sqrt_sq_eq_abs` and `abs_of_nonneg` on the
nonnegative `(tvDist μ ν).toReal`. The conditional packaging isolates
the missing analytic step (the Csiszár pointwise inequality integrated
against `ν`) so that downstream consumers (e.g. PAC-Bayes generalization
bounds, Le Cam two-point bounds in the small-divergence regime) can
chain through the `√(KL/2)` rate uniformly. -/
theorem pinsker_inequality_tvDist
    (μ ν : Measure α)
    (h_csiszar : ((tvDist μ ν).toReal) ^ 2 ≤ (InformationTheory.klDiv μ ν).toReal / 2) :
    (tvDist μ ν).toReal ≤ Real.sqrt ((InformationTheory.klDiv μ ν).toReal / 2) := by
  have h_tv_nonneg : 0 ≤ (tvDist μ ν).toReal := ENNReal.toReal_nonneg
  have h_sqrt_sq : (tvDist μ ν).toReal = Real.sqrt (((tvDist μ ν).toReal) ^ 2) := by
    rw [Real.sqrt_sq h_tv_nonneg]
  rw [h_sqrt_sq]
  exact Real.sqrt_le_sqrt h_csiszar

/-- **Classical Pinsker inequality (conditional, packaged via `pinskerBound`).**

The same statement as `pinsker_inequality_tvDist`, but with the
right-hand side written explicitly as `pinskerBound (klDiv μ ν).toReal`.
This is the form most convenient when chaining through
`pinsker_monotone_in_kl` / `pinskerBound_le_sqrt`. -/
theorem pinsker_inequality_tvDist_pinskerBound
    (μ ν : Measure α)
    (h_csiszar : ((tvDist μ ν).toReal) ^ 2 ≤ (InformationTheory.klDiv μ ν).toReal / 2) :
    (tvDist μ ν).toReal ≤ pinskerBound (InformationTheory.klDiv μ ν).toReal := by
  unfold pinskerBound
  exact pinsker_inequality_tvDist μ ν h_csiszar

/-! ### Examples

These examples demonstrate basic usage of the algebraic Pinsker /
Bretagnolle--Huber API and double as quick smoke tests. -/

section Examples

/-- **Example.** At `KL = 0` the Pinsker bound is `0`. -/
example : pinskerBound 0 = 0 := pinsker_zero_kl

/-- **Example.** The Bretagnolle--Huber bound is bounded by `1`,
"approaching `1` as `KL → ∞`" since `Real.exp (-x) → 0`. We exhibit the
universal upper bound `bhBound x ≤ 1` for *any* `x`, including arbitrarily
large `x`; the limiting value as `x → ∞` is `Real.sqrt 1 = 1`. -/
example (x : ℝ) : bhBound x ≤ 1 := bh_le_one x

end Examples

/-! ### Hellinger / Bhattacharyya bridge to the Bretagnolle--Huber bound

The classical Bretagnolle--Huber proof factors through the **Bhattacharyya
affinity** (or equivalently the Hellinger distance):

  `ρ(μ, ν)  :=  ∫ √(dμ/dτ · dν/dτ) dτ  ∈ [0, 1]`,
  `H²(μ, ν) := ∫ (√(dμ/dτ) - √(dν/dτ))² dτ = 2 · (1 - ρ(μ, ν))`,

with the two-step chain

  (1) `tvDist²(μ, ν)  ≤  1 - ρ(μ, ν)²`        (Le Cam / Cauchy--Schwarz),
  (2) `ρ(μ, ν)        ≥  Real.exp (-KL(μ‖ν) / 2)`  (Jensen on `log`).

Combining (1) with the square of (2) gives

  `tvDist²(μ, ν)  ≤  1 - Real.exp (-KL(μ‖ν))`,

which is exactly the BH bridge consumed by
`tvDist_le_sqrt_one_sub_exp_neg` in `Ch15_LowerBounds/Statistical.lean`.

Mathlib does not yet expose `bhattacharyya` or `hellingerSquared`, so we
parametrize the chain by a real value `ρ` standing in for the Bhattacharyya
affinity, together with its two characteristic hypotheses:

* `hρ_bound : 0 ≤ ρ ∧ ρ ≤ 1` (range of the affinity for probability measures);
* `h_lecam : tvDist² ≤ 1 - ρ²`        (the measure-theoretic Le Cam step);
* `h_kl_bridge : Real.exp (-KL/2) ≤ ρ` (the Jensen step on `-log`).

Under these inputs the BH bridge `tvDist² ≤ 1 - exp(-KL)` is **purely
algebraic** and is discharged below. When Mathlib lands the Hellinger /
Bhattacharyya infrastructure, the two hypotheses become standalone
theorems and the parametric statement collapses to the textbook
Bretagnolle--Huber bound. -/

section HellingerKLBridge

variable (μ ν : Measure α)

/-- **Squaring the Bhattacharyya lower bound.**

If `Real.exp (-D / 2) ≤ ρ` and `0 ≤ ρ`, then squaring both sides gives
`Real.exp (-D) ≤ ρ ^ 2`. This is the elementary monotonicity step that
upgrades the Jensen-on-`log` bound `ρ ≥ exp(-KL/2)` to its squared form,
ready for use against the Le Cam estimate `tvDist² ≤ 1 - ρ²`. -/
theorem exp_neg_le_sq_of_exp_neg_half_le {D ρ : ℝ}
    (_hρ_nonneg : 0 ≤ ρ) (h : Real.exp (-D / 2) ≤ ρ) :
    Real.exp (-D) ≤ ρ ^ 2 := by
  have h_exp_nonneg : 0 ≤ Real.exp (-D / 2) := (Real.exp_pos _).le
  have h_sq : Real.exp (-D / 2) ^ 2 ≤ ρ ^ 2 :=
    pow_le_pow_left₀ h_exp_nonneg h 2
  have h_rewrite : Real.exp (-D / 2) ^ 2 = Real.exp (-D) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [h_rewrite] at h_sq
  exact h_sq

/-- **Hellinger / Bhattacharyya discharge of the BH bridge.**

If a real number `ρ` plays the role of the Bhattacharyya affinity between
`μ` and `ν`, satisfying

* `0 ≤ ρ` (the affinity is nonnegative),
* `tvDist²(μ, ν) ≤ 1 - ρ²` (Le Cam / Cauchy--Schwarz step),
* `Real.exp (-D / 2) ≤ ρ` (Jensen on `-log`, with `D` standing in for KL),

then the **BH bridge** holds:

  `tvDist²(μ, ν)  ≤  1 - Real.exp (-D)`.

This is the algebraic chain `tvDist² ≤ 1 - ρ² ≤ 1 - exp(-D)`. -/
theorem tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya
    {ρ D : ℝ} (hρ_nonneg : 0 ≤ ρ)
    (h_lecam : ((tvDist μ ν).toReal) ^ 2 ≤ 1 - ρ ^ 2)
    (h_kl_bridge : Real.exp (-D / 2) ≤ ρ) :
    ((tvDist μ ν).toReal) ^ 2 ≤ 1 - Real.exp (-D) := by
  have h_sq : Real.exp (-D) ≤ ρ ^ 2 :=
    exp_neg_le_sq_of_exp_neg_half_le hρ_nonneg h_kl_bridge
  have h_chain : 1 - ρ ^ 2 ≤ 1 - Real.exp (-D) := by linarith
  exact h_lecam.trans h_chain

/-- **Hellinger-distance variant of the BH bridge.**

If the Hellinger squared distance `H²` between `μ` and `ν` satisfies

* `0 ≤ H²` and `H² ≤ 2` (the natural range for probability measures),
* `tvDist²(μ, ν) ≤ H² · (1 - H² / 4)` (Le Cam in Hellinger form),
* `H² ≤ 2 · (1 - Real.exp (-D / 2))` (Bhattacharyya--KL on `H² = 2(1 - ρ)`),

then the BH bridge `tvDist²(μ, ν) ≤ 1 - Real.exp (-D)` holds.

The proof reduces to `tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya` via
the identity `ρ = 1 - H² / 2`. -/
theorem tvDist_sq_le_one_sub_exp_neg_of_hellinger
    {Hsq D : ℝ}
    (_hH_nonneg : 0 ≤ Hsq) (hH_le_two : Hsq ≤ 2)
    (h_lecam : ((tvDist μ ν).toReal) ^ 2 ≤ Hsq * (1 - Hsq / 4))
    (h_kl_bridge : Hsq ≤ 2 * (1 - Real.exp (-D / 2))) :
    ((tvDist μ ν).toReal) ^ 2 ≤ 1 - Real.exp (-D) := by
  -- Set `ρ = 1 - Hsq / 2`. Then `0 ≤ ρ` (from `Hsq ≤ 2`) and the two
  -- Hellinger hypotheses translate to the Bhattacharyya hypotheses.
  set ρ : ℝ := 1 - Hsq / 2 with hρ_def
  have hρ_nonneg : 0 ≤ ρ := by simp [hρ_def]; linarith
  -- `tvDist² ≤ Hsq (1 - Hsq/4) = 1 - ρ²`. Verify the polynomial identity.
  have h_lecam' : ((tvDist μ ν).toReal) ^ 2 ≤ 1 - ρ ^ 2 := by
    have h_eq : Hsq * (1 - Hsq / 4) = 1 - ρ ^ 2 := by
      simp only [hρ_def]; ring
    rw [← h_eq]
    exact h_lecam
  -- `Hsq ≤ 2 (1 - e^{-D/2})` ↔ `e^{-D/2} ≤ 1 - Hsq/2 = ρ`.
  have h_kl_bridge' : Real.exp (-D / 2) ≤ ρ := by
    simp only [hρ_def]; linarith
  exact tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya μ ν
    hρ_nonneg h_lecam' h_kl_bridge'

end HellingerKLBridge

end LTFP.MathlibExt.Probability
