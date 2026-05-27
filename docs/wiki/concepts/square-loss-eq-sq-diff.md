# squareLoss as (z-y)² (definitional anchor)

**ID:** `square-loss-eq-sq-diff`  
**Chapter:** Ch02 (Bach §2.2.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/square-loss-eq-sq-diff/`](../../../tasks/square-loss-eq-sq-diff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — squareLoss as (z − y)² (definitional anchor)

**Concept ID:** `square-loss-eq-sq-diff`
**Chapter:** Ch 2
**Section:** 2.2.1
**Pages:** 26
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

This is the **definitional equation** for the square loss, given by Bach
verbatim in the list of canonical losses, §2.2.1 (p. 26):

> Regression: `Y = R` and `ℓ(y, z) = (y − z)²` (square loss).

The Lean orientation flips the arguments to put the **prediction first** —
`squareLoss z y = (z − y)²` — for API convenience. The equation
`squareLoss z y = (z − y)²` is then the **definitional unfolding** of our
chosen Lean form.

## Proof (verbatim)

Bach treats this as the *definition* of the square loss; no proof is needed.

In Lean: `rfl` (definitional equality after the chosen unfolding).

## Notes

- The Lean argument order is purely conventional. Bach's `(y − z)²` and our
  `(z − y)²` agree because the square is symmetric (`square-loss-symm`).
- This is the **anchor** lemma that ties the named definition `squareLoss` back
  to its formula; downstream proofs invoke this rewrite once and then operate
  on the explicit `(z − y)²`.
- One-line Lean discharge.

## Prerequisites (Bach's dependency graph)

- [`square-loss`](./square-loss.md) — Squared loss ℓ(z, y) = (z − y)²

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `squareLoss_eq_sq_diff`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

