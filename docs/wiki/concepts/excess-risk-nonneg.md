# Excess risk is nonneg under nonneg loss

**ID:** `excess-risk-nonneg`  
**Chapter:** Ch02 (Bach §2.2.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/excess-risk-nonneg/`](../../../tasks/excess-risk-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Excess risk is nonneg under nonneg loss

**Concept ID:** `excess-risk-nonneg`
**Chapter:** Ch 2
**Section:** 2.2.3 (Bayes Risk and Bayes Predictor)
**Pages:** 29
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

**Definition 2.3 (Excess risk), p. 29:**

> The excess risk of a function `f : X → Y` is equal to `R(f) − R∗`
> (it is always nonnegative).

Bach states the nonnegativity directly in the definition itself.

## Proof (verbatim, p. 29)

Implicit in the proof of Proposition 2.1:

> Proof. We have
>
>     R(f) − R∗ = R(f) − R(f∗) = ∫_X [r(f(x') | x') − min_{z ∈ Y} r(z | x')] dp(x'),
>
> which shows the proposition.

The integrand `r(f(x') | x') − min_z r(z | x') ≥ 0` pointwise. By monotonicity
of the integral, `R(f) − R∗ ≥ 0`.

## Notes

- The Lean target follows directly from `bayes-risk-le-population-risk`:
  `excessRisk f = R(f) − R∗ ≥ 0 ↔ R∗ ≤ R(f)`. The two are equivalent.
- Foundational for **every** generalization bound: bounds always have the
  form `excess risk ≤ (small quantity)`, which is meaningful only because
  the excess risk is `≥ 0`.
- One-line in Lean: `sub_nonneg.mpr (bayes_risk_le_population_risk _ _)`.

## Prerequisites (Bach's dependency graph)

- [`bayes-risk-le-population-risk`](./bayes-risk-le-population-risk.md) — Bayes risk ≤ any specific population risk

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `excess_risk_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

