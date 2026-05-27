# squareLoss midpoint convexity (algebraic core)

**ID:** `square-loss-convex`  
**Chapter:** Ch02 (Bach §2.2.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Convex`

## Statement

_See textbook excerpt below or [`tasks/square-loss-convex/`](../../../tasks/square-loss-convex/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — squareLoss midpoint convexity (algebraic core)

**Concept ID:** `square-loss-convex`
**Chapter:** Ch 2
**Section:** 2.2.1 (loss definition) and 4.1 (convex surrogates)
**Pages:** 26 (loss list)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The square loss `ℓ(y, z) = (y − z)²` is **convex in the prediction `z`** for
each fixed `y`. Bach uses this property implicitly throughout chapter 3
(linear least squares is a convex optimization) and chapter 4 (square loss as
the canonical convex surrogate for the 0–1 loss).

The algebraic core needed for Lean is the **midpoint inequality**:
for all `z₁, z₂, y ∈ R`,

    ((z₁ + z₂)/2 − y)² ≤ ½ (z₁ − y)² + ½ (z₂ − y)².

Equivalently (after expansion), the "parallelogram-law-style" identity

    ½ a² + ½ b² − ((a+b)/2)² = ¼ (a − b)² ≥ 0,

instantiated at `a = z₁ − y`, `b = z₂ − y`.

## Proof (verbatim)

Bach does not prove this in §2.2.1; it is the elementary fact that `x²` is a
convex function of `x ∈ R`. The midpoint convexity inequality is the algebraic
identity above.

In Lean: `nlinarith` or `ring_nf; positivity` will close it; alternatively
invoke `convexOn_pow 2`.

## Notes

- The squared term `(z₁ − z₂)²/4` is the **deficit** in the midpoint convexity
  inequality — Bach refers to this kind of quadratic remainder when discussing
  strong convexity in chapter 5 (gradient descent for least squares).
- This is the local-algebra anchor; full convexity over all convex combinations
  (not just midpoints) follows by standard chaining or by invoking
  `ConvexOn.pow 2`.
- One-line discharge in Lean via `nlinarith [sq_nonneg (z₁ - z₂)]`.

## Prerequisites (Bach's dependency graph)

- [`square-loss`](./square-loss.md) — Squared loss ℓ(z, y) = (z − y)²

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `squareLoss_convex_anchor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

