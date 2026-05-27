# Gaussian NLL minus 0 is nonneg

**ID:** `gaussian-nll-sub-zero-nonneg`  
**Chapter:** Ch14 (Bach §14.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gaussian`

## Statement

_See textbook excerpt below or [`tasks/gaussian-nll-sub-zero-nonneg/`](../../../tasks/gaussian-nll-sub-zero-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gaussian NLL minus 0 is nonneg

**Concept ID:** `gaussian-nll-sub-zero-nonneg`
**Chapter:** Ch 14
**Section:** §14.1.1 "Conditional Likelihoods"
**Pages:** 411 (book); PDF page 427
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — implicit in Bach)

Bach (p.411, Exercise 14.1) gives Gaussian NLL = `(1/(2σ²)) (x − μ)² + ...`.
For the σ=1, constants-dropped wrapper, `gaussianNLL μ y = (y − μ)²/2`,
which is `≥ 0` because it is half a real square.

The "minus 0" form `gaussianNLL μ y − 0 ≥ 0` is `gaussianNLL μ y ≥ 0`
after arithmetic.

## Notes

- This is a trivial consequence of `(y − μ)² ≥ 0` (squares are
  nonneg) and `2 > 0`.
- Bach does not state nonnegativity of the NLL explicitly; it is
  implicit in any NLL minimization formulation.
- Discharge: `unfold gaussianNLL; positivity` or
  `div_nonneg (sq_nonneg _) (by norm_num)`.

## Prerequisites (Bach's dependency graph)

- [`gaussian-nll`](./gaussian-nll.md) — Gaussian negative log-likelihood (square loss + const)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/LogLikelihood.lean`
- **Theorem/def name:** `gaussianNLL_sub_zero_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

