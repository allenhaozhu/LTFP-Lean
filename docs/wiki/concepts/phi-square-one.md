# phiSquare 1 = 0 (well-classified zero)

**ID:** `phi-square-one`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-square-one/`](../../../tasks/phi-square-one/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — phiSquare 1 = 0 (well-classified zero)

**Concept ID:** `phi-square-one`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 73 (definitional)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
The square surrogate vanishes at the canonical margin u = 1:
$$\Phi_{\text{square}}(1) = (1 - 1)^2 = 0.$$

## Proof (verbatim)
(Trivial by definition.)

## Notes
- Defining property: the minimum of Φ_square is at u = 1 (correct margin).
- Together with Φ_square(0) = 1, anchors the canonical "0 ↔ 1" pair.
- Pedagogical: marks the unique zero of Φ_square (cf. `phi-square-zero-iff`).

## Prerequisites (Bach's dependency graph)

- [`phi-square`](./phi-square.md) — Square surrogate Φ(u) = (u-1)²

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiSquare_one`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

