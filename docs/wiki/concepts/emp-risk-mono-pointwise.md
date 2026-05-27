# Empirical risk is pointwise-monotone

**ID:** `emp-risk-mono-pointwise`  
**Chapter:** Ch02 (Bach §2.3.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/emp-risk-mono-pointwise/`](../../../tasks/emp-risk-mono-pointwise/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Empirical risk is pointwise-monotone

**Concept ID:** `emp-risk-mono-pointwise`
**Chapter:** Ch 2
**Section:** 2.2.2 (Risks)
**Pages:** 27
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From Definition 2.2 (p. 27):

>     R̂(f) = (1/n) Σ_{i=1}^n ℓ(yi, f(xi)).

For two predictors `f, g : X → Y` and a fixed training sample, if

    ℓ(yi, f(xi)) ≤ ℓ(yi, g(xi))   for all `i = 1, …, n`,

then averaging preserves the inequality:

>     R̂(f) ≤ R̂(g).

This is the **monotonicity of the empirical risk in the pointwise losses**.

## Proof (verbatim)

Not stated by Bach; immediate from `Finset.sum_le_sum` (pointwise sum
monotonicity) and `div_le_div_of_nonneg_right` (dividing by a positive
constant preserves inequality).

In Lean:
```
exact div_le_div_of_nonneg_right (Finset.sum_le_sum hpt) (by positivity)
```

## Notes

- Empirical analog of monotonicity of the integral.
- Used implicitly in any reduction argument where we replace a complicated
  loss with a simpler upper-bounding surrogate (e.g., bounding 0–1 loss by
  hinge or square loss — chapter 4).
- The **pointwise hypothesis** is across the training sample, not across all
  of `X × Y`; it is therefore the right form for sample-dependent bounds.
- One-line discharge in Lean.

## Prerequisites (Bach's dependency graph)

- [`empirical-risk`](./empirical-risk.md) — Empirical risk R̂_n(f)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/ERM.lean`
- **Theorem/def name:** `empiricalRisk_mono_pointwise`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

