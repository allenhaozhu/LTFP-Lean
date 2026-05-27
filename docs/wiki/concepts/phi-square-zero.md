# phiSquare 0 = 1

**ID:** `phi-square-zero`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-square-zero/`](../../../tasks/phi-square-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — phiSquare 0 = 1

**Concept ID:** `phi-square-zero`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 73 (definitional)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
$$\Phi_{\text{square}}(0) = (0 - 1)^2 = 1.$$

## Proof (verbatim)
(Trivial by definition.)

## Notes
- Anchors Φ_square at the decision boundary; together with Φ_square(1) = 0 pins down the parabola.
- Used in calibration comparisons (square vs hinge vs logistic).

## Prerequisites (Bach's dependency graph)

- [`phi-square`](./phi-square.md) — Square surrogate Φ(u) = (u-1)²

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiSquare_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

