# Lower bound: m ≤ X ⇒ m ≤ E[X]

**ID:** `expectation-ge-const`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Lower-bound`

## Statement

_See textbook excerpt below or [`tasks/expectation-ge-const/`](../../../tasks/expectation-ge-const/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Lower bound: m ≤ X ⇒ m ≤ E[X]

**Concept ID:** `expectation-ge-const`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (corollary of expectation-mono + expectation-const)
**Pages:** 134-138 (book)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If $m \le X$ almost surely (with $m$ a constant) and $\mu$ is a probability
measure, then $m \le \mathbb{E}[X]$.

The dual of `expectation-le-const`; Bach uses such two-sided bounds silently
when arguing about iterates that stay in a bounded region.

## Proof (verbatim)

Combination of `expectation-mono` ($m \le X$ a.s. gives $\mathbb{E}[m] \le \mathbb{E}[X]$)
and `expectation-const` ($\mathbb{E}[m] = m$).

## Notes

- Lean form: `(∀ᵐ x ∂μ, m ≤ X x) → IsProbabilityMeasure μ → m ≤ ∫ x, X x ∂μ`.
- Pair with `expectation-le-const` to produce `expectation-in-interval`.

## Prerequisites (Bach's dependency graph)

- [`expectation-const`](./expectation-const.md) — E[c] = c under probability measure
- [`expectation-mono`](./expectation-mono.md) — Expectation is monotone

## Dependents (concepts that use this)

- [`expectation-in-interval`](./expectation-in-interval.md) — m ≤ X ≤ M ⇒ m ≤ E[X] ≤ M

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_ge_const_of_ge`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

