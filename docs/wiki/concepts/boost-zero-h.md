# Boosting with zero weak learners gives zero

**ID:** `boost-zero-h`  
**Chapter:** Ch10 (Bach §10.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Boosting/Ensemble`

## Statement

_See textbook excerpt below or [`tasks/boost-zero-h/`](../../../tasks/boost-zero-h/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Boosting with zero weak learners gives zero

**Concept ID:** `boost-zero-h`
**Chapter:** Ch 10
**Section:** 10.3 "Boosting" (algebraic sanity)
**Pages:** 299-300
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Algebraic sanity lemma for the boosted predictor of §10.3.1. When every weak
learner is the zero function `h t x = 0`, the boosted predictor is the zero
function regardless of the coefficients:

    boostedPredictor α (fun _ _ => 0) T x = 0.

Bach does not state this explicitly — it is the dual of `boost-zero-coeffs`
and follows immediately from equation (10.8) (page 299) with `φ(·, w) ≡ 0`.

## Proof (verbatim)
Definitional. `Σ_t α t · 0 = Σ_t 0 = 0`.

## Notes
- Sanity check used to validate that the `boostedPredictor` definition does
  not depend on the structure of the weak-learner family beyond its
  evaluation map.
- Technique in one line: each summand has a zero factor; the whole sum is
  zero.
- No ambiguity — purely algebraic.

## Prerequisites (Bach's dependency graph)

- [`boosted-predictor`](./boosted-predictor.md) — Boosted predictor: weighted sum of weak learners

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch10_Ensemble/Boosting.lean`
- **Theorem/def name:** `boostedPredictor_zero_h`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

