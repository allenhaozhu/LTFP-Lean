# PAC-Bayes KL = ∞ iff non-AC or non-integrable

**ID:** `pacbayes-kl-eq-top-iff`  
**Chapter:** Ch14 (Bach §14.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `PAC-Bayes`, `KL-divergence`

## Statement

_See textbook excerpt below or [`tasks/pacbayes-kl-eq-top-iff/`](../../../tasks/pacbayes-kl-eq-top-iff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — PAC-Bayes KL = ∞ iff non-AC or non-integrable

**Concept ID:** `pacbayes-kl-eq-top-iff`
**Chapter:** Ch 14
**Section:** §14.4.2 (PAC-Bayes uses KL); not stated explicitly by Bach
**Pages:** 424 (book); PDF page 440
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — Bach treats AC and integrability implicitly)

Bach (§14.4.2, p.424) defines `D(ρ‖q) = ∫_Θ log(dρ/dq)(θ) dρ(θ)`.
The Lean iff:

    pacBayesKL ρ q = ∞  ↔  ¬(ρ ≪ q ∧ Integrable (log ∘ (dρ/dq)) ρ).

This is the contrapositive of `pacbayes-kl-ne-top-iff` and the
PAC-Bayes specialization of `kl-eq-top-iff`.

## Notes

- Pair with `pacbayes-kl-ne-top-iff`. Both are Mathlib housekeeping
  facts; Bach states neither.
- Discharge: `unfold pacBayesKL; exact kl_eq_top_iff` or
  `Iff.not (pacbayes_kl_ne_top_iff ...)`.

## Prerequisites (Bach's dependency graph)

- [`kl-eq-top-iff`](./kl-eq-top-iff.md) — KL = ∞ iff non-AC or non-integrable
- [`pac-bayes-kl`](./pac-bayes-kl.md) — PAC-Bayes KL divergence wrapper

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/PACBayes.lean`
- **Theorem/def name:** `pacBayesKL_eq_top_iff`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

