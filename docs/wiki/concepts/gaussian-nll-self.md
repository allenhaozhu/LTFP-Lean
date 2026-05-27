# Gaussian NLL vanishes when prediction = truth

**ID:** `gaussian-nll-self`  
**Chapter:** Ch14 (Bach §14.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gaussian`

## Statement

_See textbook excerpt below or [`tasks/gaussian-nll-self/`](../../../tasks/gaussian-nll-self/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gaussian NLL vanishes when prediction = truth

**Concept ID:** `gaussian-nll-self`
**Chapter:** Ch 14
**Section:** §14.1.1 "Conditional Likelihoods"
**Pages:** 411 (book); PDF page 427
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — implicit in Bach via Exercise 14.1)

Bach (p.411, Exercise 14.1):

> the negative log density of the Gaussian distribution with mean μ
> and variance σ² is `(1/(2σ²)) (x − μ)² + (1/2) log(2π) + (1/2) log σ²`.

When `μ = x` (prediction equals truth), the data-dependent term
`(1/(2σ²)) (x − μ)² = 0`. For the σ=1, constants-dropped wrapper
`gaussianNLL μ y = (y − μ)² / 2`, evaluating at `μ = y` gives
`(y − y)² / 2 = 0`.

## Notes

- This is the trivial "loss at correct prediction = 0" property:
  `gaussianNLL μ μ = 0`. Bach does not state it explicitly; it follows
  from the form of the Gaussian density at its mode.
- Discharge: `unfold gaussianNLL; simp` or `ring`.
- Pairs with `gaussian-nll-zero-disp` (the displacement-form
  statement of the same fact).

## Prerequisites (Bach's dependency graph)

- [`gaussian-nll`](./gaussian-nll.md) — Gaussian negative log-likelihood (square loss + const)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/LogLikelihood.lean`
- **Theorem/def name:** `gaussianNLL_self`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

