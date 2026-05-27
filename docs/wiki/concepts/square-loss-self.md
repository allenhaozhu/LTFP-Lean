# squareLoss y y = 0

**ID:** `square-loss-self`  
**Chapter:** Ch02 (Bach §2.2.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/square-loss-self/`](../../../tasks/square-loss-self/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — squareLoss y y = 0

**Concept ID:** `square-loss-self`
**Chapter:** Ch 2
**Section:** 2.2.1
**Pages:** 26
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For the square loss `ℓ(y, z) = (y − z)²`, the "perfect prediction is zero loss"
identity is `ℓ(y, y) = (y − y)² = 0² = 0`. Bach treats this as obvious; it
is one half of `square-loss-zero-iff`.

## Proof (verbatim)

Not proved; algebraic fact `0² = 0`.

In Lean: `by simp` or `by ring`.

## Notes

- Combined with `square-loss-nonneg`, this confirms `0` is the **minimum value**
  of the square loss as a function of its arguments. Bach uses this when arguing
  that the 0–1 loss (`square-loss-self` analogue: `1_{y ≠ y} = 0`) and the square
  loss share the property that perfect predictions cost nothing.
- The dual fact `square-loss-zero-iff` ensures `y` is the **unique** minimizer.
- Foundational for `bayes-risk-nonneg` in the noise-free case.

## Prerequisites (Bach's dependency graph)

- [`square-loss`](./square-loss.md) — Squared loss ℓ(z, y) = (z − y)²

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `squareLoss_self`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

