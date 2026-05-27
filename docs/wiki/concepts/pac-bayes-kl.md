# PAC-Bayes KL divergence wrapper

**ID:** `pac-bayes-kl`  
**Chapter:** Ch14 (Bach §14.4, p. 423)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `PAC-Bayes`, `KL-divergence`

## Statement

_See textbook excerpt below or [`tasks/pac-bayes-kl/`](../../../tasks/pac-bayes-kl/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — PAC-Bayes KL divergence wrapper

**Concept ID:** `pac-bayes-kl`
**Chapter:** Ch 14
**Section:** §14.4.2 "Uniformly Bounded Loss Functions" (uses KL from §15.1.3)
**Pages:** 424 (book); PDF page 440
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim)

In Bach's PAC-Bayes derivation (§14.4.2, p.424), the KL divergence
that arrives via Donsker-Varadhan is defined as:

> [...] with P(θ) the set of probability distributions on Θ and
> D(ρ‖q) the Kullback-Leibler (KL) divergence between ρ and q, defined
> as follows (see also section 15.1.3):
>
>     D(ρ‖q)  =  ∫_Θ  log( dρ/dq )(θ) · dρ(θ).

This is the integrated form: Radon-Nikodym derivative `dρ/dq`, taken in
log, integrated against `ρ`. Bach uses the prior `q` as the reference
measure and the posterior `ρ` as the integrating measure.

## Notes

- This is the *PAC-Bayes-specific* wrapper: the input measures are
  (posterior, prior) over the *parameter* space Θ, not over data. The
  bound's RHS is `D(ρ‖q)` where `ρ` is data-dependent (the Gibbs
  posterior) and `q` is fixed before seeing data.
- Bach's notation `D(ρ‖q)` matches Mathlib's `InformationTheory.klDiv ρ q`
  exactly (same argument order, same `dρ/dq` Radon-Nikodym convention).
- All `pac-bayes-*` lemmas in the registry (zero prior, non-AC,
  non-integrable, etc.) are housekeeping facts that follow directly
  from the underlying `klDiv` Mathlib lemmas via this wrapper. Bach
  does not discuss any of these edge cases (he assumes `ρ ≪ q` and
  the integrand is integrable, implicitly).
- Bach's only use of this KL in Ch 14 is inside §14.4.2 (Eq. 14.5 and
  Eq. 14.6 — the only places in the entire chapter where KL appears).

## Prerequisites (Bach's dependency graph)

- [`infotheory-foundation`](./infotheory-foundation.md) — Information-theory foundation: KL divergence wrapper

## Dependents (concepts that use this)

- [`pac-bayes-kl-not-ac`](./pac-bayes-kl-not-ac.md) — PAC-Bayes KL = ∞ when posterior not absolutely continuous
- [`pac-bayes-mcallester`](./pac-bayes-mcallester.md) — McAllester PAC-Bayes bound (algebraic core anchor)
- [`pac-bayes-zero-prior`](./pac-bayes-zero-prior.md) — PAC-Bayes with zero prior is ∞
- [`pacbayes-kl-def`](./pacbayes-kl-def.md) — PAC-Bayes KL definition unfolded
- [`pacbayes-kl-eq-top-iff`](./pacbayes-kl-eq-top-iff.md) — PAC-Bayes KL = ∞ iff non-AC or non-integrable
- [`pacbayes-kl-ne-top-iff`](./pacbayes-kl-ne-top-iff.md) — PAC-Bayes KL non-top iff AC + integrable

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/PACBayes.lean`
- **Theorem/def name:** `pacBayesKL`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

