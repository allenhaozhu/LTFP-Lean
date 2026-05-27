# Boosting with single weak learner

**ID:** `boost-one-step`  
**Chapter:** Ch10 (Bach §10.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Boosting/Ensemble`

## Statement

_See textbook excerpt below or [`tasks/boost-one-step/`](../../../tasks/boost-one-step/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Boosting with single weak learner

**Concept ID:** `boost-one-step`
**Chapter:** Ch 10
**Section:** 10.3 "Boosting" (algebraic sanity)
**Pages:** 299-301
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Algebraic sanity lemma: when the boosting horizon is `T = 1`, the boosted
predictor collapses to a single coefficient-weighted weak learner:

    boostedPredictor α h 1 x = α 0 · h 0 x.

Bach uses this implicitly at the start of §10.3.2 (page 301, equation 10.10):

> "Starting from the function `g_0 = 0`, we thus consider the simplest update
>
>     g_t = g_{t-1} + b_t · φ(·, w_t),                              (10.10)
>
> where the linear combination coefficients `b_1, …, b_{t-1}` for
> `φ(·, w_1), …, φ(·, w_{t-1})` are not changed once they are computed."

After the first update (`t = 1`), `g_1 = b_1 · φ(·, w_1)`, which in Lean's
indexing is `boostedPredictor α h 1 x = α 0 · h 0 x`.

## Proof (verbatim)
Definitional. `Σ_{t=0}^{0} α t · h t x = α 0 · h 0 x`.

## Notes
- Validates the base case of the §10.3.2 incremental update (equation 10.10,
  page 301).
- Technique in one line: unfold the single-term sum.
- No ambiguity — purely algebraic.

## Prerequisites (Bach's dependency graph)

- [`boosted-predictor`](./boosted-predictor.md) — Boosted predictor: weighted sum of weak learners

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch10_Ensemble/Boosting.lean`
- **Theorem/def name:** `boostedPredictor_one_step`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

