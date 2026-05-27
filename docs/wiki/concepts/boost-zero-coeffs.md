# Boosting with zero coefficients gives zero predictions

**ID:** `boost-zero-coeffs`  
**Chapter:** Ch10 (Bach §10.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Boosting/Ensemble`

## Statement

_See textbook excerpt below or [`tasks/boost-zero-coeffs/`](../../../tasks/boost-zero-coeffs/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Boosting with zero coefficients gives zero predictions

**Concept ID:** `boost-zero-coeffs`
**Chapter:** Ch 10
**Section:** 10.3 "Boosting" (algebraic sanity)
**Pages:** 299-300
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Algebraic sanity lemma for the boosted predictor of §10.3.1. When every
coefficient `α t = 0`, the boosted predictor is the zero function:

    boostedPredictor (fun _ => 0) h T x = 0.

Bach does not state this as a separate proposition — it is the obvious
degenerate case of equation (10.8) (page 299) with `ν ≡ 0`. The
incremental learning algorithm of §10.3.2 (equation 10.10, page 301)
starts from `g_0 = 0`, which in Lean is exactly the all-zero-coefficient
initialization.

## Proof (verbatim)
Definitional. `Σ_t 0 · h t x = Σ_t 0 = 0`.

## Notes
- Sanity check guarding the `boostedPredictor` definition; required so that
  the §10.3.2 initialization `g_0 = 0` (page 301) is consistent with the
  closed-form sum.
- Technique in one line: each summand is zero; the whole sum is zero.
- No ambiguity — purely algebraic.

## Prerequisites (Bach's dependency graph)

- [`boosted-predictor`](./boosted-predictor.md) — Boosted predictor: weighted sum of weak learners

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch10_Ensemble/Boosting.lean`
- **Theorem/def name:** `boostedPredictor_zero_coeffs`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

