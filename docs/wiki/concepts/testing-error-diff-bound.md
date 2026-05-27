# Testing error difference ≤ 1

**ID:** `testing-error-diff-bound`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/testing-error-diff-bound/`](../../../tasks/testing-error-diff-bound/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Testing error difference ≤ 1

**Concept ID:** `testing-error-diff-bound`
**Chapter:** Ch 15
**Section:** §15.1 (probability-bound chaining)
**Pages:** 430-434 (book) / 446-450 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.testing_error_diff_bound`.
Difference of two testing-error probabilities is bounded by 1:

> If `p ≤ 1` and `q ≥ 0`, then `p − q ≤ 1`.

Trivial consequence of the unit-interval constraint on each probability.

## Proof (verbatim)

Bach §15.1.4 (p. 434), Cor 15.1 (Eq. 15.8) provides the canonical
upper bound on testing error:

> "Corollary 15.1 (Fano's inequality for multiple hypothesis testing).
> Given M probability distributions p_{θ_j}, j = 1,...,M, on D, then
>
>     inf_h (1/M) ∑_{j=1}^M P_{θ_j}(h(D) ≠ j)
>       ≥ 1 − (1/(M² log M)) ∑_{j,j'=1}^M D_KL(p_{θ_j} ‖ p_{θ_j'})
>             − log 2 / log M.                               (15.8)"

Each `P_{θ_j}(h(D) ≠ j) ∈ [0,1]`, so any difference `p − q` with
`p ≤ 1`, `q ≥ 0` is `≤ 1 − 0 = 1`. Bach uses this implicitly when
algebraically simplifying the RHS of Eq. 15.8.

## Notes

- **Bach's technique in one line:** probabilities live in [0,1];
  their pairwise differences live in [−1, 1].
- Lean proof: `by linarith`.

## Prerequisites (Bach's dependency graph)

- [`testing-error-nonneg`](./testing-error-nonneg.md) — Statistical lower-bound anchor: testing error nonneg

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `testing_error_diff_bound`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

