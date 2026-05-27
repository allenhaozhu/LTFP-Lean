# Gaussian NLL = (y - μ)² / 2 (definitional)

**ID:** `gaussian-nll-eq-sqdisp`  
**Chapter:** Ch14 (Bach §14.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gaussian`

## Statement

_See textbook excerpt below or [`tasks/gaussian-nll-eq-sqdisp/`](../../../tasks/gaussian-nll-eq-sqdisp/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gaussian NLL = (y − μ)² / 2 (definitional)

**Concept ID:** `gaussian-nll-eq-sqdisp`
**Chapter:** Ch 14
**Section:** §14.1.1 "Conditional Likelihoods"
**Pages:** 411 (book); PDF page 427
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim)

Bach (p.411):

> For least-squares regression, we can interpret the loss
> `(1/2) (yᵢ − fθ(xᵢ))²` as a Gaussian model with mean `fθ(xᵢ)` and
> variance 1.

So the σ=1, constants-dropped Gaussian NLL is exactly `½ (y − μ)²`.

Exercise 14.1 (p.411) gives the full Gaussian NLL with all constants:

> `−log p(y|μ, σ) = (1/(2σ²)) (x − μ)² + (1/2) log(2π) + (1/2) log σ²`

For σ = 1 this reduces to `½ (x − μ)² + ½ log(2π)`, and dropping the
y-independent constant `½ log(2π)` (irrelevant for minimization) gives
the Lean wrapper.

## Notes

- This is the *definition* of the Lean wrapper, not a derived lemma:
  `gaussianNLL μ y = (y − μ)² / 2` by `rfl` once the definition is
  unfolded.
- The σ = 1 reduction is Bach's explicit choice in the second sentence
  of §14.1.1.
- Discharge in Lean: `rfl` or `unfold gaussianNLL`.

## Prerequisites (Bach's dependency graph)

- [`gaussian-nll`](./gaussian-nll.md) — Gaussian negative log-likelihood (square loss + const)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/LogLikelihood.lean`
- **Theorem/def name:** `gaussianNLL_eq_squared_displacement`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

