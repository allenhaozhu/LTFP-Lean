# KL with zero right measure is ∞

**ID:** `kl-zero-right`  
**Chapter:** Ch14 (Bach §F5)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `KL-divergence`

## Statement

_See textbook excerpt below or [`tasks/kl-zero-right/`](../../../tasks/kl-zero-right/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — KL with zero right measure is ∞

**Concept ID:** `kl-zero-right`
**Chapter:** Ch 14 (registry); §15.1.3 by Bach
**Section:** §15.1.3 KL definition
**Pages:** 433-434 (book); PDF pages 449-450
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — Bach treats AC implicitly)

Bach (p.433):

> Given two distributions on Z, p and q (which are nonnegative
> functions on Z that sum to 1), then the KL divergence is defined as
>
>     D_KL(p‖q)  =  ∑_{z ∈ Z}  p(z) · log( p(z) / q(z) ).

When `q ≡ 0` (the zero measure on the right), `p(z) / q(z) = p(z) / 0`
is undefined for any `z` with `p(z) > 0`. By the Mathlib convention,
`klDiv p 0 = ∞` (the "absolutely continuous w.r.t. zero" condition
fails unless p itself is the zero measure, but klDiv takes probability
measures so p is not zero).

Bach **does not state** this case. It is a corollary of `kl-of-not-ac`
specialized to `q = 0`.

## Notes

- This is one of four KL housekeeping concepts (`kl-of-not-ac`,
  `kl-zero-right`, `kl-eq-top-iff`, `kl-ne-top-iff`). All four are
  Mathlib facts; Bach uses none of them explicitly.
- Operationally: KL is asymmetric in (p, q); the right argument must
  "cover" the left for KL to be finite. The zero right measure is the
  extreme failure of coverage.
- Discharge: `simp [klDiv, ...]` once the underlying Mathlib lemma is
  in scope (Mathlib likely names it `klDiv_zero_right` or similar).

## Prerequisites (Bach's dependency graph)

- [`infotheory-foundation`](./infotheory-foundation.md) — Information-theory foundation: KL divergence wrapper

## Dependents (concepts that use this)

- [`pac-bayes-zero-prior`](./pac-bayes-zero-prior.md) — PAC-Bayes with zero prior is ∞

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/InfoTheory.lean`
- **Theorem/def name:** `kl_zero_right`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

