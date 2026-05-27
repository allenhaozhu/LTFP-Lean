# phiLogistic 0 = log 2

**ID:** `phi-logistic-zero`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-logistic-zero/`](../../../tasks/phi-logistic-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — phiLogistic 0 = log 2

**Concept ID:** `phi-logistic-zero`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74 (definitional)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
$$\Phi_{\text{logistic}}(0) = \log(1 + e^{0}) = \log 2.$$

## Proof (verbatim)
(Trivial by definition.)

## Notes
- Definitional anchor for the logistic surrogate at 0.
- Φ_logistic(0) = log 2 is the entropy of a uniform Bernoulli — natural max-entropy reference.
- Φ'_logistic(0) = −1/2, so Φ_logistic is calibrated (Prop. 4.1) and equals "−log 2 σ" at 0.

## Prerequisites (Bach's dependency graph)

- [`phi-logistic`](./phi-logistic.md) — Logistic surrogate Φ(u) = log(1 + exp(-u))

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiLogistic_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

