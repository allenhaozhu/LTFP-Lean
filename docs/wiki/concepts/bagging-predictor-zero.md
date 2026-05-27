# Bagging zero predictors yields zero

**ID:** `bagging-predictor-zero`  
**Chapter:** Ch10 (Bach §10.1.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Boosting/Ensemble`

## Statement

_See textbook excerpt below or [`tasks/bagging-predictor-zero/`](../../../tasks/bagging-predictor-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bagging zero predictors yields zero

**Concept ID:** `bagging-predictor-zero`
**Chapter:** Ch 10
**Section:** 10.1.2 "Bagging" (algebraic sanity)
**Pages:** 286-288
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Algebraic sanity lemma for the bagged predictor of §10.1.2: when every
sub-predictor is the zero function, the bagged predictor is also zero:

    baggingPredictor (fun _ _ => 0) x = 0.

Bach does not state this explicitly — it is a definitional consequence of

    f̂(x) = (1/B) Σ_b f̂^(b)(x)

(page 286). It is registered as a Lean-side anchor so downstream §10.1.2
arguments can substitute the zero predictor without re-deriving the average.

## Proof (verbatim)
Definitional. `Σ_b 0 = 0`, so `(1/B) · 0 = 0`.

## Notes
- Sanity check guarding the `baggingPredictor` definition against off-by-one
  issues when `B = 0` (empty sum) or when every sub-predictor is zero.
- Technique in one line: unfold the average; apply `Finset.sum_const_zero`.
- No ambiguity — purely algebraic.

## Prerequisites (Bach's dependency graph)

- [`bagging-predictor`](./bagging-predictor.md) — Bagging: average of B sub-predictors

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch10_Ensemble/RandomProjections.lean`
- **Theorem/def name:** `baggingPredictor_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

