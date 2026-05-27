# PAC-Bayes with zero prior is ∞

**ID:** `pac-bayes-zero-prior`  
**Chapter:** Ch14 (Bach §14.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `PAC-Bayes`

## Statement

_See textbook excerpt below or [`tasks/pac-bayes-zero-prior/`](../../../tasks/pac-bayes-zero-prior/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — PAC-Bayes with zero prior is ∞

**Concept ID:** `pac-bayes-zero-prior`
**Chapter:** Ch 14
**Section:** §14.4.2 (PAC-Bayes); not stated explicitly by Bach
**Pages:** 424 (book); PDF page 440
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — implicit in Bach)

Bach (§14.4.2, p.424) defines the PAC-Bayes KL as
`D(ρ‖q) = ∫_Θ log(dρ/dq)(θ) · dρ(θ)`. When `q = 0` (zero prior over
parameter space), `dρ/dq` is undefined for any θ in the support of ρ.
By the Mathlib convention, `klDiv ρ 0 = ∞`.

This is the PAC-Bayes specialization of `kl-zero-right`.

## Notes

- Operationally: a zero prior assigns no mass to any parameter, so no
  posterior `ρ` can be absolutely continuous w.r.t. it. The bound's
  complexity term is ∞.
- Bach does not state this edge case; it is a corollary of his KL
  definition + the Mathlib `∞` convention.
- Discharge: `unfold pacBayesKL; exact klDiv_zero_right` or analogous,
  once `kl-zero-right` is in scope.

## Prerequisites (Bach's dependency graph)

- [`kl-zero-right`](./kl-zero-right.md) — KL with zero right measure is ∞
- [`pac-bayes-kl`](./pac-bayes-kl.md) — PAC-Bayes KL divergence wrapper

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/PACBayes.lean`
- **Theorem/def name:** `pacBayesKL_zero_prior`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

