# Gaussian NLL symmetric in (μ, y)

**ID:** `gaussian-nll-symm`  
**Chapter:** Ch14 (Bach §14.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gaussian`

## Statement

_See textbook excerpt below or [`tasks/gaussian-nll-symm/`](../../../tasks/gaussian-nll-symm/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gaussian NLL symmetric in (μ, y)

**Concept ID:** `gaussian-nll-symm`
**Chapter:** Ch 14
**Section:** §14.1.1 "Conditional Likelihoods"
**Pages:** 411 (book); PDF page 427
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — implicit in Bach, explicit in Exercise 14.1)

> **Exercise 14.1.** Show that the negative log density of the
> Gaussian distribution with mean μ and variance σ² (i.e.,
> `−log p(y|μ, σ) = (1/(2σ²)) (x − μ)² + (1/2) log(2π) + (1/2) log σ²`)
> is not convex in (μ, σ²) but is jointly convex in (μ/σ², σ⁻²).

Bach uses `(x − μ)²` which equals `(μ − x)²` — symmetry of the
quadratic form in `(μ, y)` is immediate from `(y − μ)² = (μ − y)²`.

## Notes

- For the σ=1 reduction used in the Lean wrapper, `gaussianNLL μ y =
  (y − μ)² / 2`, swapping (μ, y) gives `(μ − y)² / 2 = (y − μ)² / 2`
  by the symmetry of the square.
- Bach does not state this as a named property; it is a one-line
  consequence of `(y − μ)² = (μ − y)²`. The Lean discharge is
  `unfold gaussianNLL; ring` or equivalent.
- This corresponds to the fact that the Gaussian likelihood is
  symmetric in (mean, observation) when σ is fixed — the geometry of
  the squared error is unchanged under swap.

## Prerequisites (Bach's dependency graph)

- [`gaussian-nll`](./gaussian-nll.md) — Gaussian negative log-likelihood (square loss + const)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/LogLikelihood.lean`
- **Theorem/def name:** `gaussianNLL_symm`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

