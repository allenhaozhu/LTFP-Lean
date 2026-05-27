# Squared loss is nonnegative

**ID:** `square-loss-nonneg`  
**Chapter:** Ch02 (Bach §2.2.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/square-loss-nonneg/`](../../../tasks/square-loss-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Squared loss is nonnegative

**Concept ID:** `square-loss-nonneg`
**Chapter:** Ch 2
**Section:** 2.2.1 / 2.2.2
**Pages:** 26-28
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Implicit in Bach's framing of the loss function as taking values in `R+`, §2.2.1
(p. 25):

> We consider a loss function `ℓ : Y × Y → R` (often `R+`) [...]

Specifically for the square loss `ℓ(y, z) = (y − z)²`:

> Regression: `Y = R` and `ℓ(y, z) = (y − z)²` (square loss). (p. 26)

Hence `squareLoss z y = (z − y)² ≥ 0` for all `z, y ∈ R` is the elementary
algebraic statement that any real square is nonnegative.

## Proof (verbatim)

Bach does not prove this; it is the elementary fact `x² ≥ 0` for `x ∈ R`
(sometimes invoked implicitly e.g. when arguing positivity of the risk on p. 27-28).

In Mathlib / Lean: `sq_nonneg : ∀ (x : ℝ), 0 ≤ x²` — single application.

## Notes

- One-line discharge via `sq_nonneg (z - y)`.
- This is the **foundational** nonnegativity fact that propagates through
  `pop-risk-nonneg`, `emp-risk-nonneg`, `bayes-risk-nonneg`, `excess-risk-nonneg`
  whenever the underlying loss is the square loss.
- No measurability, no integrability — pure algebra.

## Prerequisites (Bach's dependency graph)

- [`square-loss`](./square-loss.md) — Squared loss ℓ(z, y) = (z − y)²

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `squareLoss_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

