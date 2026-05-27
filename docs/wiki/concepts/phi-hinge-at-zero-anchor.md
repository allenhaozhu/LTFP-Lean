# phiHinge 0 = 1 (alias)

**ID:** `phi-hinge-at-zero-anchor`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-hinge-at-zero-anchor/`](../../../tasks/phi-hinge-at-zero-anchor/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — phiHinge 0 = 1 (alias / anchor form)

**Concept ID:** `phi-hinge-at-zero-anchor`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74 (definitional)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
$$\Phi_{\text{hinge}}(0) = 1.$$

(This is identical content to `phi-hinge-zero`; it is the "anchor" alias used in places
where the proof needs the literal numeric value of Φ_hinge at the decision boundary.)

## Proof (verbatim)
(Trivial.) Φ_hinge(0) = max(1 − 0, 0) = max(1, 0) = 1.

## Notes
- Duplicate naming convention: `phi-hinge-zero` and `phi-hinge-at-zero-anchor` both refer
  to Φ_hinge(0) = 1; the second is used in chain-of-equalities anchoring.
- Definitional unfolding.

## Prerequisites (Bach's dependency graph)

- [`phi-hinge`](./phi-hinge.md) — Hinge surrogate Φ(u) = max(1-u, 0) — yields SVM

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiHinge_at_zero_is_one`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

