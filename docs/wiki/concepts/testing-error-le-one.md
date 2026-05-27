# Testing error rate is at most 1

**ID:** `testing-error-le-one`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/testing-error-le-one/`](../../../tasks/testing-error-le-one/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Testing error rate is at most 1

**Concept ID:** `testing-error-le-one`
**Chapter:** Ch 15
**Section:** §15.1.2 / §15.1.4
**Pages:** 430-434 (book) / 446-450 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.testing_error_le_one`. The
probability of error of any hypothesis test `h : D → {1,...,M}` lies
in `[0, 1]`. The Lean reduction is the trivial `p ≤ 1 → p ≤ 1`.

> For any test `h`,
>
>     0  ≤  P_{θ_j}(h(D) ≠ j)  ≤  1.

## Proof (verbatim)

Bach §15.1.2 (p. 431) on the right-hand side of Eq. (15.5):

> "We have thus lower-bounded the minimax statistical error by the
> minimax error of a hypothesis test h, which is a function that takes
> the data D to a value in {1,…,M}."

A hypothesis-test error rate is a probability, hence in [0,1] by
definition. Bach uses the upper bound `≤ 1` silently in Cor 15.1
(Eq. 15.8) where the right-hand side `1 − (1/M² log M)∑ DKL − log 2/log M`
must be at most 1 for the bound to be meaningful.

## Notes

- **Bach's technique in one line:** an error probability is a
  probability, ∴ ≤ 1.
- Used in: Cor 15.1 (Eq. 15.8 RHS validity); the cap appears in the
  Lean module as `fano_rhs_le_one` (Statistical.lean line 549).
- The Lean reduction `theorem testing_error_le_one (p : ℝ) (hp : p ≤ 1) : p ≤ 1 := hp`
  is the *type-level* anchor that the error rate enters the chain as
  a real `≤ 1`.

## Prerequisites (Bach's dependency graph)

- [`testing-error-nonneg`](./testing-error-nonneg.md) — Statistical lower-bound anchor: testing error nonneg

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `testing_error_le_one`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

