# PAC-Bayes KL non-top iff AC + integrable

**ID:** `pacbayes-kl-ne-top-iff`  
**Chapter:** Ch14 (Bach §14.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `PAC-Bayes`, `KL-divergence`

## Statement

_See textbook excerpt below or [`tasks/pacbayes-kl-ne-top-iff/`](../../../tasks/pacbayes-kl-ne-top-iff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — PAC-Bayes KL non-top iff AC + integrable

**Concept ID:** `pacbayes-kl-ne-top-iff`
**Chapter:** Ch 14
**Section:** §14.4.2 (PAC-Bayes uses KL); not stated explicitly by Bach
**Pages:** 424 (book); PDF page 440
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — Bach treats AC and integrability implicitly)

Bach (§14.4.2, p.424) defines the PAC-Bayes KL:

> D(ρ‖q)  =  ∫_Θ  log( dρ/dq )(θ) · dρ(θ).

For this integral to be a finite real number, we need:
1. `ρ ≪ q` (posterior absolutely continuous w.r.t. prior), and
2. `log(dρ/dq)` is `ρ`-integrable.

The Lean iff:

    pacBayesKL ρ q ≠ ∞  ↔  (ρ ≪ q ∧ Integrable (log ∘ (dρ/dq)) ρ).

Bach **does not state** this iff explicitly; it is the PAC-Bayes
specialization of `kl-ne-top-iff`.

## Notes

- This is the iff downstream code needs to discharge "PAC-Bayes bound
  is meaningful" from "(ρ, q) is a nice pair."
- Bach uses this case implicitly in §14.4.2.
- Discharge: `unfold pacBayesKL; exact kl_ne_top_iff` or analogous.

## Prerequisites (Bach's dependency graph)

- [`kl-ne-top-iff`](./kl-ne-top-iff.md) — KL ≠ ∞ iff absolutely continuous and integrable
- [`pac-bayes-kl`](./pac-bayes-kl.md) — PAC-Bayes KL divergence wrapper

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/PACBayes.lean`
- **Theorem/def name:** `pacBayesKL_ne_top_iff`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

