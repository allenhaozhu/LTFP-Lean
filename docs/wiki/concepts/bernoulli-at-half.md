# Bernoulli NLL at p = 1/2 = log 2

**ID:** `bernoulli-at-half`  
**Chapter:** Ch14 (Bach §14.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/bernoulli-at-half/`](../../../tasks/bernoulli-at-half/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bernoulli NLL at p = 1/2 = log 2

**Concept ID:** `bernoulli-at-half`
**Chapter:** Ch 14
**Section:** §14.1.1 "Conditional Likelihoods"
**Pages:** 411 (book); PDF page 427
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — implicit in Bach)

Bach (p.411) gives `p(yᵢ|xᵢ) = sigmoid(yᵢ fθ(xᵢ))` for y ∈ {−1, 1}.
For the {0, 1} reparameterization,
`bernoulliNLL p y = − y log p − (1 − y) log(1 − p)`.

At `p = 1/2`, both `log p` and `log(1 − p)` equal `log(1/2) = −log 2`,
so `bernoulliNLL (1/2) y = −y · (−log 2) − (1 − y) · (−log 2)
= y log 2 + (1 − y) log 2 = log 2` (for any y ∈ {0, 1}).

## Notes

- This is the "uniform prior" baseline: when the model predicts
  probability `1/2` for both classes, the per-sample NLL is `log 2`,
  regardless of the true label. This is the maximum-entropy / no-info
  baseline.
- Bach does not state this explicitly; it is a one-line evaluation of
  the Bernoulli NLL formula at the symmetric point.
- Discharge: `unfold bernoulliNLL; simp [Real.log_inv, Real.log_two];
  ring` or evaluate by cases on `y = 0` vs `y = 1`.

## Prerequisites (Bach's dependency graph)

- [`bernoulli-nll`](./bernoulli-nll.md) — Bernoulli negative log-likelihood (logistic loss in disguise)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/LogLikelihood.lean`
- **Theorem/def name:** `bernoulliNLL_at_half`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

