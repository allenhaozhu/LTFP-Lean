# Bernoulli NLL at p=0, y=0 is 0

**ID:** `bernoulli-nll-correct-zero`  
**Chapter:** Ch14 (Bach §14.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/bernoulli-nll-correct-zero/`](../../../tasks/bernoulli-nll-correct-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bernoulli NLL at p = 0, y = 0 is 0

**Concept ID:** `bernoulli-nll-correct-zero`
**Chapter:** Ch 14
**Section:** §14.1.1 "Conditional Likelihoods"
**Pages:** 411 (book); PDF page 427
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — implicit in Bach)

Bach (p.411): logistic loss as conditional log-likelihood. For the
{0, 1} parameterization, `bernoulliNLL p y = − y log p − (1 − y) log(1 − p)`.

At `(p, y) = (0, 0)`:
- `y = 0` zeroes out the first term: `− 0 · log 0 = 0` (using the
  standard convention `0 · log 0 = 0`).
- `(1 − y) log(1 − p) = 1 · log(1 − 0) = log 1 = 0`.

So `bernoulliNLL 0 0 = 0`.

## Notes

- This is the trivial "loss at correct prediction with full confidence
  = 0" property for the `y = 0` class.
- Bach does not state this explicitly; it is a one-line evaluation.
- The `0 · log 0 = 0` convention is standard in info theory and is
  what Mathlib uses for the negative-entropy `negMulLog` function.
- Discharge: `unfold bernoulliNLL; simp` (Mathlib's `simp` should
  resolve `0 * Real.log 0 = 0` and `Real.log 1 = 0`).

## Prerequisites (Bach's dependency graph)

- [`bernoulli-nll`](./bernoulli-nll.md) — Bernoulli negative log-likelihood (logistic loss in disguise)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/LogLikelihood.lean`
- **Theorem/def name:** `bernoulliNLL_correct_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

