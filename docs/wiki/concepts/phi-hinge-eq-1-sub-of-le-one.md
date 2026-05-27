# Hinge equals 1 - u on u ≤ 1

**ID:** `phi-hinge-eq-1-sub-of-le-one`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-hinge-eq-1-sub-of-le-one/`](../../../tasks/phi-hinge-eq-1-sub-of-le-one/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Hinge equals 1 − u on u ≤ 1

**Concept ID:** `phi-hinge-eq-1-sub-of-le-one`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74 (definitional)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
For every u ≤ 1, the hinge surrogate equals its affine branch:
$$\Phi_{\text{hinge}}(u) = \max(1 - u, 0) = 1 - u.$$

## Proof (verbatim)
(Trivial by definition.) For u ≤ 1, 1 − u ≥ 0, hence max(1 − u, 0) = 1 − u.

## Notes
- Complementary case to `phi-hinge-zero-of-ge-one`.
- On u ≤ 1 the hinge equals an affine function 1 − u → its right-derivative at 0 is −1 < 0,
  which gives classification calibration (Proposition 4.1, p. 78).

## Prerequisites (Bach's dependency graph)

- [`phi-hinge`](./phi-hinge.md) — Hinge surrogate Φ(u) = max(1-u, 0) — yields SVM

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiHinge_eq_one_sub_of_le_one`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

