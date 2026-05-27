/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.Ch15_LowerBounds.Statistical

/-!
# LTlib example — Bach §15.1 Pinsker / Bretagnolle–Huber walkthrough

This file is a *worked walkthrough* of the **Bretagnolle–Huber
inequality**, the textbook total-variation-vs-KL bound that
generalises Pinsker's inequality in the high-divergence regime.
We use the named carrier
`LTFP.tvDist_le_sqrt_one_sub_exp_neg_klDiv` (in
`LTFP/Ch15_LowerBounds/Statistical.lean`), which depends on the
Le Cam step and Jensen step landed locally in
`LTFP/MathlibExt/Probability/Distance/Bhattacharyya.lean`.

It is **pedagogical**: every `example` here unfolds the named carrier
at a concrete shape, with rich inline commentary tying each step back
to Bach's textbook proof (Bach 2024, *Learning Theory from First
Principles*, §15.1, pp. 427-440) and Tsybakov's standard reference
(Tsybakov, *Introduction to Nonparametric Estimation*, 2009, §2.4).

## How to read this file

Open it in VS Code with the Lean 4 extension. Place the cursor on each
`example`, `#check`, or `exact` and the infoview shows the goal at
that step. Reading load: ≈45 minutes.

## Bach's proof of Bretagnolle–Huber (book pp. 427-440)

Bach derives Bretagnolle–Huber from two textbook lemmas that together
sandwich the **Bhattacharyya coefficient** `ρ(μ, ν) := ∫ √(dμ/dν) dν`
between the total-variation distance and the KL divergence:

* **Le Cam / Cauchy–Schwarz step** (Bach §15.1, also Tsybakov §2.4):
    `tvDist²(μ, ν)  ≤  1 − ρ(μ, ν)²`.
  *Proof sketch.* Apply Cauchy–Schwarz to
    `tvDist(μ, ν) = ½ ∫ |√(dμ/dν) − √(dν/dν)|² dν`,
  yielding `tvDist² ≤ (1 − ρ)(1 + ρ) = 1 − ρ²`. Formalised in
  `LTFP.MathlibExt.Probability.tvDist_sq_le_one_sub_bhattacharyya_sq`.

* **Jensen step** (Bach §15.1):
    `ρ(μ, ν)  ≥  exp(− KL(μ ‖ ν) / 2)`.
  *Proof sketch.* Apply Jensen's inequality to the concave function
  `√` and the measure `μ`, using `ρ = ∫ √(dν/dμ) dμ` and the log-link
  to KL. Formalised in
  `LTFP.MathlibExt.Probability.bhattacharyya_ge_exp_neg_half_klDiv`.

Chaining the two:
    `tvDist²  ≤  1 − ρ²  ≤  1 − exp(−KL)`,
which yields the Bretagnolle–Huber inequality after `√`:
    `tvDist(μ, ν)  ≤  √(1 − exp(−KL(μ ‖ ν)))`.

In the small-KL regime, this recovers Pinsker (`tvDist² ≤ KL / 2`) up
to a constant, but it is uniformly bounded by `1` — unlike Pinsker —
making it the right tool when KL is moderate or large.

## The carrier theorem used

```text
LTFP.tvDist_le_sqrt_one_sub_exp_neg_klDiv
  (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hμν : μ ≪ ν) (hkl : InformationTheory.klDiv μ ν ≠ ∞) :
    (LTFP.MathlibExt.Probability.tvDist μ ν).toReal ≤
      Real.sqrt (1 − Real.exp (-(InformationTheory.klDiv μ ν).toReal))
```

Read this as: "If `μ ≪ ν` and `KL(μ ‖ ν) < ∞`, then the total-variation
distance is bounded by `√(1 − exp(−KL))`." No `0 ≤ D` side condition is
required because `klDiv` is non-negative; no Le Cam or Jensen-bridge
hypothesis is required because both are now A-class theorems in
`Bhattacharyya.lean`.

-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace LTFP.Examples.PinskerBH

universe u

variable {α : Type u} [MeasurableSpace α]

/-! ### Step 1 — Sanity-check the named carrier exists with the
expected signature. -/

-- The Bretagnolle–Huber inequality (Bach §15.1, A-class).
#check @LTFP.tvDist_le_sqrt_one_sub_exp_neg_klDiv

-- The Hellinger-route companion (same conclusion, factored through the
-- Hellinger-squared distance instead of the Bhattacharyya coefficient).
#check @LTFP.tvDist_le_sqrt_one_sub_exp_neg_klDiv_via_hellinger

/-! ### Step 2 — Concrete Bretagnolle–Huber inequality.

We instantiate `tvDist_le_sqrt_one_sub_exp_neg_klDiv` at two arbitrary
probability measures `μ, ν` on a measurable space `α`, with the only
non-trivial hypotheses being:

  * `μ ≪ ν` — the standard absolute-continuity prerequisite for KL,
    Bach pp. 428-429.
  * `KL(μ ‖ ν) ≠ ∞` — the finiteness condition needed to make
    `exp(−KL)` meaningful (otherwise the RHS is `√1 = 1` and the
    inequality reduces to `tvDist ≤ 1`, which already holds
    unconditionally).

The proof is one line — `exact` the carrier — because the carrier
already encapsulates Bach's two-step Le Cam + Jensen proof.
-/

example
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hkl : klDiv μ ν ≠ ∞) :
    (LTFP.MathlibExt.Probability.tvDist μ ν).toReal ≤
      Real.sqrt (1 - Real.exp (-(klDiv μ ν).toReal)) := by
  -- The textbook proof — Le Cam (Cauchy–Schwarz on the Hellinger
  -- integral) ↦ Jensen on `√` against the Bhattacharyya coefficient
  -- ↦ chain `tvDist² ≤ 1 − ρ² ≤ 1 − exp(−KL)` ↦ apply `√` — is fully
  -- encapsulated by the named carrier. Cursor on the carrier name to
  -- see the exact signature in the infoview.
  exact LTFP.tvDist_le_sqrt_one_sub_exp_neg_klDiv μ ν hμν hkl

/-! ### Step 3 — Hellinger-route companion.

Bach (§15.1) and Tsybakov (§2.4) both present an alternate derivation
through the **squared Hellinger distance**
  `Hsq(μ, ν) := 2 (1 − ρ(μ, ν))`.
The Le Cam step then reads
  `tvDist²  ≤  Hsq · (1 − Hsq / 4)`,
and the KL bridge reads
  `Hsq  ≤  2 (1 − exp(−KL / 2))`.

These are equivalent to the Bhattacharyya forms via the algebraic
identity `Hsq (1 − Hsq/4) = 1 − ρ²` (with `ρ = 1 − Hsq/2`); see
`LTFP/MathlibExt/Probability/Distance/Bhattacharyya.lean`.

We demonstrate that the Hellinger route lands at the **same**
conclusion as the Bhattacharyya route — Bretagnolle–Huber is
route-independent.
-/

example
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hkl : klDiv μ ν ≠ ∞) :
    (LTFP.MathlibExt.Probability.tvDist μ ν).toReal ≤
      Real.sqrt (1 - Real.exp (-(klDiv μ ν).toReal)) := by
  -- Hellinger-route discharge. Same conclusion as Step 2, different
  -- internal proof structure. Useful for cross-checking the algebra of
  -- `Hsq (1 - Hsq/4) = 1 - ρ²`.
  exact LTFP.tvDist_le_sqrt_one_sub_exp_neg_klDiv_via_hellinger μ ν hμν hkl

/-! ### Step 4 — Bretagnolle–Huber as a uniform `tvDist ≤ 1` bound.

In the large-KL regime, the RHS `√(1 − exp(−KL))` approaches `1` from
below — it never exceeds `1`. So BH **always** gives a non-vacuous
bound on `tvDist`, unlike Pinsker (`tvDist ≤ √(KL/2)`) which becomes
vacuous when `KL > 2`.

This is the headline pedagogical reason Bach (§15.1) prefers
Bretagnolle–Huber for the lower-bound machinery of statistical
estimation: it survives the high-KL regime that arises when the prior
distribution puts very different mass than the posterior.

The carrier `tvDist_le_one_of_bh_bridge` gives the `tvDist ≤ 1`
consequence directly — derivable from BH but stated as a separate
lemma for callers who only want the `≤ 1` ceiling.
-/

example
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hkl : klDiv μ ν ≠ ∞) :
    (LTFP.MathlibExt.Probability.tvDist μ ν).toReal ≤ 1 := by
  -- Chain Bretagnolle–Huber with `√(1 - exp(-D)) ≤ 1` (which holds
  -- because `0 ≤ exp(-D)`, so `1 - exp(-D) ≤ 1`, so `√` is ≤ 1).
  have h_BH : (LTFP.MathlibExt.Probability.tvDist μ ν).toReal ≤
      Real.sqrt (1 - Real.exp (-(klDiv μ ν).toReal)) :=
    LTFP.tvDist_le_sqrt_one_sub_exp_neg_klDiv μ ν hμν hkl
  -- `1 - exp(-D) ≤ 1` since `0 ≤ exp(-D)`.
  have h_arg_le_one : 1 - Real.exp (-(klDiv μ ν).toReal) ≤ 1 := by
    have : 0 ≤ Real.exp (-(klDiv μ ν).toReal) := (Real.exp_pos _).le
    linarith
  -- `√(·) ≤ √1 = 1` by monotonicity of `√`.
  have h_sqrt_le_one :
      Real.sqrt (1 - Real.exp (-(klDiv μ ν).toReal)) ≤ 1 := by
    have h1 : Real.sqrt (1 - Real.exp (-(klDiv μ ν).toReal)) ≤ Real.sqrt 1 :=
      Real.sqrt_le_sqrt h_arg_le_one
    simpa using h1
  -- Chain.
  exact h_BH.trans h_sqrt_le_one

end LTFP.Examples.PinskerBH
