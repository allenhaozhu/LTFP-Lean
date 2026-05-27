# Squared loss is symmetric

**ID:** `square-loss-symm`  
**Chapter:** Ch02 (Bach §2.2.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/square-loss-symm/`](../../../tasks/square-loss-symm/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Squared loss is symmetric

**Concept ID:** `square-loss-symm`
**Chapter:** Ch 2
**Section:** 2.2.1
**Pages:** 26
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For the square loss `ℓ(y, z) = (y − z)²`, the symmetry `ℓ(y, z) = ℓ(z, y)`
is immediate from `(y − z)² = (z − y)²`. Bach notes the convention ambiguity
explicitly (p. 26):

> Some authors swap `y` and `z` in the definition of the loss.

For the square loss this swap is harmless (unlike, e.g., asymmetric pinball or
false-positive/false-negative cost-sensitive losses — see Exercise 2.1, p. 29-30).

## Proof (verbatim)

Bach does not prove this. The fact reduces to `(a)² = (-a)²`, instantiated at
`a = y − z`.

In Lean: `by ring` (or rewrite via `neg_sub` + `sq_abs`).

## Notes

- Single algebraic line: `(z − y)² = (y − z)²`.
- One of the structural properties Bach exploits implicitly when arguing that
  the Bayes predictor `f∗(x) = E[y | x]` is well-defined for square-loss
  regression (p. 30); the symmetry is what allows the `min` over `z` to factor
  via the standard variance/mean decomposition.
- Useful for downstream API: ensures `squareLoss z y` and `squareLoss y z` are
  interchangeable in lemmas about the square risk.

## Prerequisites (Bach's dependency graph)

- [`square-loss`](./square-loss.md) — Squared loss ℓ(z, y) = (z − y)²

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `squareLoss_symm`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

