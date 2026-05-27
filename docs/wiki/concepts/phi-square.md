# Square surrogate Φ(u) = (u-1)²

**ID:** `phi-square`  
**Chapter:** Ch04 (Bach §4.1.1, p. 73)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-square/`](../../../tasks/phi-square/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Square surrogate Φ(u) = (u−1)²

**Concept ID:** `phi-square`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 73
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Quadratic/square loss: Φ(u) = (u − 1)². Since y² = 1 for y ∈ {−1, 1}, we have
Φ(y g(x)) = (y − g(x))² = (g(x) − y)². "We get back least-squares regression, ignore that
the labels have to belong to {−1, 1}, and take the sign of g(x) for the prediction."

## Proof (verbatim)
(Definition — no proof.) Bach also remarks:

"Note the overpenalization for a large positive value of yg(x) that will not be present
for the other losses discussed next (which are nonincreasing)."

## Notes
- Convex; differentiable everywhere with Φ'(0) = −2 < 0, so classification-calibrated
  (by Proposition 4.1).
- Symmetric around u = 1: Φ(1 − v) = Φ(1 + v) = v².
- Zero only at u = 1 (the "correct margin").
- Drives the linear discriminant analysis / least-squares regression viewpoint of classification.

## Prerequisites (Bach's dependency graph)

- [`convex-foundation`](./convex-foundation.md) — Convex analysis foundation: L-smooth alias + Mathlib re-exports

## Dependents (concepts that use this)

- [`phi-square-1-lt-0`](./phi-square-1-lt-0.md) — phiSquare 1 < phiSquare 0
- [`phi-square-one`](./phi-square-one.md) — phiSquare 1 = 0 (well-classified zero)
- [`phi-square-symm-around-1`](./phi-square-symm-around-1.md) — phiSquare symmetric around u = 1
- [`phi-square-zero`](./phi-square-zero.md) — phiSquare 0 = 1
- [`phi-square-zero-iff`](./phi-square-zero-iff.md) — phiSquare u = 0 ↔ u = 1

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiSquare`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

