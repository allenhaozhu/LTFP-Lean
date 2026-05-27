# phiSquare 1 < phiSquare 0

**ID:** `phi-square-1-lt-0`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-square-1-lt-0/`](../../../tasks/phi-square-1-lt-0/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — phiSquare 1 < phiSquare 0

**Concept ID:** `phi-square-1-lt-0`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 73 (definitional consequence)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
$$\Phi_{\text{square}}(1) = 0 < 1 = \Phi_{\text{square}}(0).$$

## Proof (verbatim)
(Trivial.) Φ_square(1) = (1−1)² = 0; Φ_square(0) = (0−1)² = 1; 0 < 1.

## Notes
- Trivial: combines `phi-square-one` and `phi-square-zero`.
- Anchors monotonicity behavior of Φ_square on [0, 1] (it decreases from 1 to 0).
- Pedagogical reference.

## Prerequisites (Bach's dependency graph)

- [`phi-square`](./phi-square.md) — Square surrogate Φ(u) = (u-1)²

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiSquare_one_lt_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

