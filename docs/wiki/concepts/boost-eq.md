# Boosted predictor = sum α t · h t x (definitional)

**ID:** `boost-eq`  
**Chapter:** Ch10 (Bach §10.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Boosting/Ensemble`

## Statement

_See textbook excerpt below or [`tasks/boost-eq/`](../../../tasks/boost-eq/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Boosted predictor = sum α t · h t x (definitional)

**Concept ID:** `boost-eq`
**Chapter:** Ch 10
**Section:** 10.3 "Boosting" (definitional restatement)
**Pages:** 299-300
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Definitional restatement of the boosted predictor (§10.3.1, page 299):

    boostedPredictor α h T x = Σ_{t=0}^{T-1} α t · h t x.

This is Bach's discrete specialization of equation (10.8) on page 299:

    f(x) = ∫_W φ(x, w) dν(w)

with `ν = Σ_{i=1}^t b_i δ_{w_i}`, restated as the simple finite sum

    f = Σ_{i=1}^t b_i · φ_i(·, w).

The Lean `boost-eq` lemma simply asserts that `boostedPredictor` unfolds to
this sum (i.e., that the Lean definition matches Bach's formula).

## Proof (verbatim)
Definitional / `rfl` after unfolding `boostedPredictor`.

## Notes
- This is a Lean-side bookkeeping lemma — it exposes the closed-form sum so
  that downstream rewrites can manipulate `boostedPredictor α h T x` as
  `Σ α t · h t x` directly.
- Technique in one line: unfold the definition.
- No ambiguity — purely structural.

## Prerequisites (Bach's dependency graph)

- [`boosted-predictor`](./boosted-predictor.md) — Boosted predictor: weighted sum of weak learners

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch10_Ensemble/Boosting.lean`
- **Theorem/def name:** `boostedPredictor_eq`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

