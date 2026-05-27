# Boosted predictor linear in coefficients α

**ID:** `boosted-add-coeff`  
**Chapter:** Ch10 (Bach §10.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Boosting/Ensemble`

## Statement

_See textbook excerpt below or [`tasks/boosted-add-coeff/`](../../../tasks/boosted-add-coeff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Boosted predictor linear in coefficients α

**Concept ID:** `boosted-add-coeff`
**Chapter:** Ch 10
**Section:** 10.3 "Boosting" (algebraic sanity)
**Pages:** 299-301
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Algebraic sanity lemma: the boosted predictor is linear in the coefficient
vector `α`:

    boostedPredictor (α + β) h T x = boostedPredictor α h T x
                                     + boostedPredictor β h T x.

Bach uses this implicitly in §10.3.2 (page 301), where the incremental
update `g_t = g_{t-1} + b_t · φ(·, w_t)` (equation 10.10) is itself a
decomposition of the coefficient vector into "previous" (`g_{t-1}` carries
coefficients `b_1, …, b_{t-1}`) plus "new" (the single coefficient `b_t`).
Linearity in `α` is what makes this incremental view algebraically equivalent
to the closed-form sum `Σ b_i · φ(·, w_i)`.

## Proof (verbatim)
Definitional. `Σ_t (α t + β t) · h t x = Σ_t α t · h t x + Σ_t β t · h t x`
by distributivity and additivity of the finite sum.

## Notes
- Linearity in `α` is a recurring algebraic ingredient: matching pursuit
  (§10.3.3, page 302) updates `b_t = −F'(u_{t-1})ᵀ ψ(w_t)`, and the running
  predictor accumulates these coefficients additively.
- Technique in one line: distribute the inner product over the sum, then
  split with `Finset.sum_add_distrib`.
- No ambiguity — purely algebraic.

## Prerequisites (Bach's dependency graph)

- [`boosted-predictor`](./boosted-predictor.md) — Boosted predictor: weighted sum of weak learners

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch10_Ensemble/Boosting.lean`
- **Theorem/def name:** `boostedPredictor_add_α`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

