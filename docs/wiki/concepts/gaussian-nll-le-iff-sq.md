# Gaussian NLL monotone in (y-μ)²

**ID:** `gaussian-nll-le-iff-sq`  
**Chapter:** Ch14 (Bach §14.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gaussian`

## Statement

_See textbook excerpt below or [`tasks/gaussian-nll-le-iff-sq/`](../../../tasks/gaussian-nll-le-iff-sq/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gaussian NLL monotone in (y − μ)²

**Concept ID:** `gaussian-nll-le-iff-sq`
**Chapter:** Ch 14
**Section:** §14.1.1 "Conditional Likelihoods"
**Pages:** 411 (book); PDF page 427
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — implicit in Bach)

Bach (p.411, Exercise 14.1) gives `gaussianNLL μ y = (y − μ)²/2` (σ=1,
constants dropped). Monotonicity in `(y − μ)²` is the trivial fact:
`a ≤ b ↔ a/2 ≤ b/2` when comparing two squared displacements.

So `gaussianNLL μ₁ y₁  ≤  gaussianNLL μ₂ y₂  ↔  (y₁ − μ₁)²  ≤  (y₂ − μ₂)²`.

## Notes

- Bach does not state this explicitly; it follows from the form of the
  density.
- The "monotone in (y − μ)²" framing is useful because all comparisons
  among Gaussian NLL values reduce to comparisons of squared residuals.
  This is the basis for least-squares regression: minimizing NLL is
  equivalent to minimizing the sum of squared residuals.
- Discharge in Lean: `unfold gaussianNLL; constructor; intro h; linarith;
  intro h; linarith` or `div_le_div_iff` then `ring_nf`.

## Prerequisites (Bach's dependency graph)

- [`gaussian-nll`](./gaussian-nll.md) — Gaussian negative log-likelihood (square loss + const)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/LogLikelihood.lean`
- **Theorem/def name:** `gaussianNLL_le_iff_sq_le`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

