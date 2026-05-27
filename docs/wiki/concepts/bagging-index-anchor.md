# Bagging index reflexivity anchor

**ID:** `bagging-index-anchor`  
**Chapter:** Ch10 (Bach §10.1.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Boosting/Ensemble`

## Statement

_See textbook excerpt below or [`tasks/bagging-index-anchor/`](../../../tasks/bagging-index-anchor/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bagging index reflexivity anchor

**Concept ID:** `bagging-index-anchor`
**Chapter:** Ch 10
**Section:** 10.1.2 "Bagging" (algebraic sanity)
**Pages:** 286-288
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Algebraic reflexivity anchor for the bagging predictor's index slot. The
bagging formula

    f̂(x) = (1/B) Σ_{b=1}^B f̂^(b)(x)

ranges `b` over `{1, …, B}`; the index-anchor lemma records that for any
fixed `b`, the indexed access `(fun b' => f̂^(b')) b = f̂^(b)` — a tiny
reflexivity fact needed when Lean's elaborator unfolds the indexed sum.

Bach does not state this; it is purely a Lean-side bookkeeping anchor.

## Proof (verbatim)
Reflexivity, i.e., `rfl` in Lean.

## Notes
- Trivial reflexivity anchor used by downstream `baggingPredictor` rewrites
  so that pattern-matching on the index slot succeeds.
- Technique in one line: `rfl`.
- No ambiguity — purely structural.

## Prerequisites (Bach's dependency graph)

- [`bagging-predictor`](./bagging-predictor.md) — Bagging: average of B sub-predictors

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch10_Ensemble/RandomProjections.lean`
- **Theorem/def name:** `baggingPredictor_index_anchor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

