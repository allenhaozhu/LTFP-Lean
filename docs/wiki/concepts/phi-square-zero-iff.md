# phiSquare u = 0 ↔ u = 1

**ID:** `phi-square-zero-iff`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-square-zero-iff/`](../../../tasks/phi-square-zero-iff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — phiSquare u = 0 ↔ u = 1

**Concept ID:** `phi-square-zero-iff`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 73 (definitional)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
The square surrogate vanishes precisely at u = 1:
$$\Phi_{\text{square}}(u) = 0 \iff u = 1.$$

## Proof (verbatim)
(Trivial.) Φ_square(u) = (u − 1)². Then (u − 1)² = 0 ⇔ u − 1 = 0 ⇔ u = 1.

## Notes
- Trivial characterization of the unique zero.
- The unique minimum of a smooth strictly convex parabola at its vertex.
- Used as a uniqueness reference for "ideal margin" arguments.

## Prerequisites (Bach's dependency graph)

- [`phi-square`](./phi-square.md) — Square surrogate Φ(u) = (u-1)²

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiSquare_eq_zero_iff`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

