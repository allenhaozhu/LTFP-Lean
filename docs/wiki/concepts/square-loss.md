# Squared loss ℓ(z, y) = (z − y)²

**ID:** `square-loss`  
**Chapter:** Ch02 (Bach §2.2.2)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/square-loss/`](../../../tasks/square-loss/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Squared loss ℓ(z, y) = (z − y)²

**Concept ID:** `square-loss`
**Chapter:** Ch 2
**Section:** 2.2.1 (Supervised Learning Problems and Loss Functions)
**Pages:** 26 (loss list) and 28 (risk specialization)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From the list of canonical losses, §2.2.1 (p. 26):

> Regression: `Y = R` and `ℓ(y, z) = (y − z)²` (square loss). The absolute loss
> `ℓ(y, z) = |y − z|` is often used for robust estimation (since the penalty for
> large errors is smaller).

Specialization of the expected risk for square loss, §2.2.2 (p. 28):

> Regression: `Y = R` and `ℓ(y, z) = (y − z)²` (square loss). The risk is then
> equal to
>
>     R(f) = E[ (y − f(x))² ],
>
> often referred to as "mean squared error."

## Proof (verbatim)

(Definition — no proof.) Bach uses the square loss throughout the regression
discussion (chapter 3 is dedicated to it).

## Notes

- **Argument convention.** Bach writes `ℓ(y, z) = (y − z)²` with truth `y` first.
  Our Lean concept `square-loss` is written as `squareLoss z y = (z − y)²` (prediction
  first). The two are equal because square is symmetric: `(y − z)² = (z − y)²`. The
  Lean choice is purely an API convenience.
- Closed-form Bayes predictor: `f∗(x) = E[y | x]` (p. 30, derived via law of total
  variance).
- The square loss is the canonical example throughout chapters 3 (linear least
  squares), 5 (gradient descent), 7 (kernel ridge regression), and 9 (neural nets
  for regression).
- Structural properties (nonnegativity, symmetry, zero-iff, etc.) are tracked as
  separate Lean lemmas; see the `square-loss-*` family of concept IDs.

## Prerequisites (Bach's dependency graph)

- [`loss-function`](./loss-function.md) — Loss function ℓ : 𝒴 × 𝒴 → ℝ

## Dependents (concepts that use this)

- [`square-loss-convex`](./square-loss-convex.md) — squareLoss midpoint convexity (algebraic core)
- [`square-loss-eq-sq-diff`](./square-loss-eq-sq-diff.md) — squareLoss as (z-y)² (definitional anchor)
- [`square-loss-nonneg`](./square-loss-nonneg.md) — Squared loss is nonnegative
- [`square-loss-self`](./square-loss-self.md) — squareLoss y y = 0
- [`square-loss-symm`](./square-loss-symm.md) — Squared loss is symmetric
- [`square-loss-zero-iff`](./square-loss-zero-iff.md) — squareLoss z y = 0 ↔ z = y

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `squareLoss`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

