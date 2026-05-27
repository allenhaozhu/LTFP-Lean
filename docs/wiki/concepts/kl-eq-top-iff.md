# KL = ∞ iff non-AC or non-integrable

**ID:** `kl-eq-top-iff`  
**Chapter:** Ch14 (Bach §F5)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `KL-divergence`

## Statement

_See textbook excerpt below or [`tasks/kl-eq-top-iff/`](../../../tasks/kl-eq-top-iff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — KL = ∞ iff non-AC or non-integrable

**Concept ID:** `kl-eq-top-iff`
**Chapter:** Ch 14 (registry); §15.1.3 by Bach
**Section:** §15.1.3 KL definition
**Pages:** 433-434 (book); PDF pages 449-450
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — Bach treats AC and integrability implicitly)

Bach (p.434):

>     D_KL(p‖q)  =  E_p [ log (dp/dq)(x) ],
>
> where dp/dq is the density of p with respect to q.

This definition requires:
1. `p ≪ q` (so `dp/dq` exists), and
2. `log(dp/dq)` is `p`-integrable.

When either condition fails, Mathlib's `klDiv` returns `∞`. The lemma
`kl-eq-top-iff` is the biconditional characterization:

    klDiv p q = ∞  ↔  ¬(p ≪ q ∧ Integrable (log ∘ (dp/dq)) p).

Bach **does not state** this biconditional explicitly. It is a
Mathlib housekeeping fact.

## Notes

- This is the "characterization" half of the (top, non-top) pair —
  the companion `kl-ne-top-iff` is the contrapositive.
- Bach uses neither explicitly; his analysis assumes both AC and
  integrability hold (typical for nice prior/posterior pairs in
  PAC-Bayes).
- Discharge: `simp [klDiv, ...]` against Mathlib's definition;
  Mathlib likely names the iff `klDiv_eq_top_iff` or similar.

## Prerequisites (Bach's dependency graph)

- [`infotheory-foundation`](./infotheory-foundation.md) — Information-theory foundation: KL divergence wrapper

## Dependents (concepts that use this)

- [`pacbayes-kl-eq-top-iff`](./pacbayes-kl-eq-top-iff.md) — PAC-Bayes KL = ∞ iff non-AC or non-integrable

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/InfoTheory.lean`
- **Theorem/def name:** `kl_eq_top_iff`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

