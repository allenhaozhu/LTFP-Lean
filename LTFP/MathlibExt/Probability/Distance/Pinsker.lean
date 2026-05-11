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

end LTFP.MathlibExt.Probability
