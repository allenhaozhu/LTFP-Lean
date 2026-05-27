# KL divergence is ∞ when not absolutely continuous

**ID:** `kl-of-not-ac`  
**Chapter:** Ch14 (Bach §F5)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `KL-divergence`

## Statement

_See textbook excerpt below or [`tasks/kl-of-not-ac/`](../../../tasks/kl-of-not-ac/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — KL divergence is ∞ when not absolutely continuous

**Concept ID:** `kl-of-not-ac`
**Chapter:** Ch 14 (registry); cross-referenced to §15.1.3
**Section:** §15.1.3 (KL definition); not stated explicitly by Bach
**Pages:** 433-434 (book); PDF pages 449-450
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — Bach gives only the AC-implicit form)

> For example, the KL divergence between two distributions can be
> defined as
>
>     D_KL(p‖q)  =  E_p [ log (dp/dq)(x) ],
>
> where dp/dq is the density of p with respect to q.

(Bach p.434, §15.1.3 "From discrete to continuous distributions".)

Bach **does not explicitly state** the `KL = ∞ when p ⊄ q` case. He
implicitly assumes `p ≪ q` whenever he writes `dp/dq`. The lemma
`kl-of-not-ac` is a Mathlib housekeeping fact: when absolute continuity
fails, `klDiv p q = ∞` by convention in Mathlib's
`InformationTheory.klDiv` definition.

## Notes

- **Bach treats this implicitly.** The discrete form
  `∑ p(z) log(p(z)/q(z))` implicitly diverges (`log(p/0) = ∞`) when
  there is `z` with `p(z) > 0` and `q(z) = 0`. Bach absorbs this into
  the "convexity of t ↦ t log t" remark without spelling out the ∞
  case.
- The Mathlib convention encodes the "p not ≪ q ⇒ klDiv = ∞" case in
  its definition; this concept is the wrapper lemma that exposes it
  for PAC-Bayes downstream consumers.
- No proof needed here beyond `simp [klDiv, ...]` against Mathlib's
  definition; no Bach-side content to translate.
- This is one of four KL housekeeping concepts (`kl-of-not-ac`,
  `kl-zero-right`, `kl-eq-top-iff`, `kl-ne-top-iff`). All four are
  Mathlib facts; Bach uses none of them explicitly.

## Prerequisites (Bach's dependency graph)

- [`infotheory-foundation`](./infotheory-foundation.md) — Information-theory foundation: KL divergence wrapper

## Dependents (concepts that use this)

- [`pac-bayes-kl-not-ac`](./pac-bayes-kl-not-ac.md) — PAC-Bayes KL = ∞ when posterior not absolutely continuous

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/InfoTheory.lean`
- **Theorem/def name:** `kl_of_not_ac`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

