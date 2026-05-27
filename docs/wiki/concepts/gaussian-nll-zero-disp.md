# Gaussian NLL at zero displacement = 0

**ID:** `gaussian-nll-zero-disp`  
**Chapter:** Ch14 (Bach §14.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gaussian`

## Statement

_See textbook excerpt below or [`tasks/gaussian-nll-zero-disp/`](../../../tasks/gaussian-nll-zero-disp/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gaussian NLL at zero displacement = 0

**Concept ID:** `gaussian-nll-zero-disp`
**Chapter:** Ch 14
**Section:** §14.1.1 "Conditional Likelihoods"
**Pages:** 411 (book); PDF page 427
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — implicit in Bach via Exercise 14.1)

Bach (p.411, Exercise 14.1) gives the Gaussian NLL as
`(1/(2σ²)) (x − μ)² + (1/2) log(2π) + (1/2) log σ²`. When the
displacement `x − μ = 0`, the data-dependent term vanishes.

For the constants-dropped, σ=1 wrapper used in the Lean target:
`gaussianNLL μ y = (y − μ)² / 2`, so `gaussianNLL μ y = 0` whenever
`y − μ = 0`.

## Notes

- This is the displacement-form companion of `gaussian-nll-self`. Same
  underlying fact: NLL evaluated at zero residual is zero.
- Bach does not state this explicitly; it is a one-line corollary of
  the closed-form density.
- Discharge: `intro h; unfold gaussianNLL; rw [sub_eq_zero.mpr h];
  simp` or analogous.

## Prerequisites (Bach's dependency graph)

- [`gaussian-nll`](./gaussian-nll.md) — Gaussian negative log-likelihood (square loss + const)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/LogLikelihood.lean`
- **Theorem/def name:** `gaussianNLL_zero_displacement`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

