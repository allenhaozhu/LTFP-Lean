# m ≤ X ≤ M ⇒ m ≤ E[X] ≤ M

**ID:** `expectation-in-interval`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-in-interval/`](../../../tasks/expectation-in-interval/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — m ≤ X ≤ M ⇒ m ≤ E[X] ≤ M

**Concept ID:** `expectation-in-interval`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (composite bound)
**Pages:** 134-138 (book)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If $m \le X \le M$ almost surely (with $m,M$ constants) and $\mu$ is a
probability measure, then $m \le \mathbb{E}[X] \le M$.

A two-sided pointwise bound transfers to a two-sided bound on the expectation.

## Proof (verbatim)

Conjunction of `expectation-ge-const` and `expectation-le-const`.

## Notes

- Lean form: `(∀ᵐ x ∂μ, m ≤ X x) → (∀ᵐ x ∂μ, X x ≤ M) → IsProbabilityMeasure μ → m ≤ ∫ x, X x ∂μ ∧ ∫ x, X x ∂μ ≤ M`.
- Used as a packaged convenience lemma; encapsulates the "bounded random
  variable" reasoning common in SGD analysis (Bach's hypothesis H-2).

## Prerequisites (Bach's dependency graph)

- [`expectation-ge-const`](./expectation-ge-const.md) — Lower bound: m ≤ X ⇒ m ≤ E[X]
- [`expectation-le-const`](./expectation-le-const.md) — Expectation bounded by a sup constant

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_in_interval`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

