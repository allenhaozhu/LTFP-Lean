# Hinge surrogate vanishes on margin ≥ 1

**ID:** `phi-hinge-zero-of-ge-one`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-hinge-zero-of-ge-one/`](../../../tasks/phi-hinge-zero-of-ge-one/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Hinge surrogate vanishes on margin ≥ 1

**Concept ID:** `phi-hinge-zero-of-ge-one`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74 (definitional)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
For every u ≥ 1, the hinge surrogate vanishes:
$$\Phi_{\text{hinge}}(u) = \max(1 - u, 0) = 0.$$

## Proof (verbatim)
(Trivial by definition.) For u ≥ 1, 1 − u ≤ 0, hence max(1 − u, 0) = 0.

## Notes
- Trivial case-split lemma.
- Pedagogical role: in well-classified examples (margin ≥ 1), the hinge loss exerts no
  pressure — sparsity of SVM support vectors arises from this property.
- Used by `phi-hinge-eq-1-sub-of-le-one` (complementary case).

## Prerequisites (Bach's dependency graph)

- [`phi-hinge`](./phi-hinge.md) — Hinge surrogate Φ(u) = max(1-u, 0) — yields SVM

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiHinge_eq_zero_of_ge_one`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

