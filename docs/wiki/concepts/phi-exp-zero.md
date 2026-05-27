# phiExponential 0 = 1

**ID:** `phi-exp-zero`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-exp-zero/`](../../../tasks/phi-exp-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — phiExponential 0 = 1

**Concept ID:** `phi-exp-zero`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74 (definitional)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
$$\Phi_{\text{exp}}(0) = \exp(-0) = 1.$$

## Proof (verbatim)
(Trivial by definition.)

## Notes
- Definitional anchor.
- Matches Φ_square(0) = 1 and Φ_hinge(0) = 1 — all three (and logistic with log 2)
  share a common "value at zero margin" of order 1, making them directly comparable.
- AdaBoost's exponential loss reduces to 1 at the decision boundary.

## Prerequisites (Bach's dependency graph)

- [`phi-exponential`](./phi-exponential.md) — Exponential surrogate Φ(u) = exp(-u) — yields AdaBoost

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiExponential_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

