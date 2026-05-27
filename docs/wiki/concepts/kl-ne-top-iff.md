# KL ≠ ∞ iff absolutely continuous and integrable

**ID:** `kl-ne-top-iff`  
**Chapter:** Ch14 (Bach §F5)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `KL-divergence`

## Statement

_See textbook excerpt below or [`tasks/kl-ne-top-iff/`](../../../tasks/kl-ne-top-iff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — KL ≠ ∞ iff absolutely continuous and integrable

**Concept ID:** `kl-ne-top-iff`
**Chapter:** Ch 14 (registry); §15.1.3 by Bach
**Section:** §15.1.3 KL definition
**Pages:** 433-434 (book); PDF pages 449-450
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — Bach treats AC and integrability implicitly)

Bach (p.434):

>     D_KL(p‖q)  =  E_p [ log (dp/dq)(x) ],
>
> where dp/dq is the density of p with respect to q.

The biconditional `kl-ne-top-iff`:

    klDiv p q ≠ ∞  ↔  (p ≪ q ∧ Integrable (log ∘ (dp/dq)) p).

This is the contrapositive of `kl-eq-top-iff`. Bach **does not state**
either form explicitly.

## Notes

- This is the "nice case" characterization: when AC holds and the
  log-Radon-Nikodym is integrable, KL is a finite real number.
- The Mathlib name is likely `klDiv_ne_top_iff` or similar.
- Bach's PAC-Bayes derivation (§14.4.2) assumes this case implicitly:
  the `D(ρ‖q)` in his bound is a finite quantity. The Lean wrapper
  needs the explicit iff for downstream proofs that condition on
  finiteness.
- Discharge: `rw [← Ne, kl_eq_top_iff]; push_neg` or
  `Iff.not (kl_eq_top_iff ...)`.

## Prerequisites (Bach's dependency graph)

- [`infotheory-foundation`](./infotheory-foundation.md) — Information-theory foundation: KL divergence wrapper

## Dependents (concepts that use this)

- [`pacbayes-kl-ne-top-iff`](./pacbayes-kl-ne-top-iff.md) — PAC-Bayes KL non-top iff AC + integrable

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/InfoTheory.lean`
- **Theorem/def name:** `kl_ne_top_iff`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

