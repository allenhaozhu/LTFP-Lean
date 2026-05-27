# phiHinge 0 = 1

**ID:** `phi-hinge-zero`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-hinge-zero/`](../../../tasks/phi-hinge-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — phiHinge 0 = 1

**Concept ID:** `phi-hinge-zero`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74 (definitional)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
$$\Phi_{\text{hinge}}(0) = \max(1 - 0, 0) = 1.$$

## Proof (verbatim)
(Trivial by definition.)

## Notes
- Definitional anchor at u = 0.
- All four canonical surrogates take value 1 at u = 0 (except logistic, which is log 2 ≈ 0.693).
- Pedagogical reference point.

## Prerequisites (Bach's dependency graph)

- [`phi-hinge`](./phi-hinge.md) — Hinge surrogate Φ(u) = max(1-u, 0) — yields SVM

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiHinge_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

