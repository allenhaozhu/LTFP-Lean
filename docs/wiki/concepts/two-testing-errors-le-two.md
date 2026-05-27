# Sum of two testing errors ≤ 2

**ID:** `two-testing-errors-le-two`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/two-testing-errors-le-two/`](../../../tasks/two-testing-errors-le-two/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Sum of two testing errors ≤ 2

**Concept ID:** `two-testing-errors-le-two`
**Chapter:** Ch 15
**Section:** §15.1 (sum of probabilities ≤ 2)
**Pages:** 430-434 (book) / 446-450 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.two_testing_errors_le_two`.
Two probabilities in [0,1] sum to at most 2:

> If `p ≤ 1` and `q ≤ 1`, then `p + q ≤ 2`.

Trivial upper bound used in averaging arguments.

## Proof (verbatim)

Bach §15.1.2 (p. 430), Eq. (15.5) RHS:

> "≥ A · inf_h (1/M) ∑_{j=1}^M P_{θ_j}( h(D) ≠ j ),     (15.5)"

Each `P_{θ_j}(h(D) ≠ j) ≤ 1`, so the sum of two such probabilities is
≤ 2; in the M = 2 case, the average `(p + q)/2 ≤ 1`. Bach uses this
silently when the average is shown to be bounded away from 1 (which is
how Fano produces the lower bound on the testing error).

## Notes

- **Bach's technique in one line:** the sum of two reals each ≤ 1 is
  ≤ 2 — `by linarith`.
- Used in M = 2 algebraic post-processing of Eq. (15.5).

## Prerequisites (Bach's dependency graph)

- [`testing-error-nonneg`](./testing-error-nonneg.md) — Statistical lower-bound anchor: testing error nonneg

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `two_testing_errors_le_two`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

