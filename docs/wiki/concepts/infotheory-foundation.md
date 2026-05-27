# Information-theory foundation: KL divergence wrapper

**ID:** `infotheory-foundation`  
**Chapter:** Ch14 (Bach §F5)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `KL-divergence`

## Statement

Wraps Mathlib.InformationTheory.KullbackLeibler — required prereq for Ch 14/15.

## Bach's textbook treatment

# Bach textbook excerpt — Information-theory foundation: KL divergence wrapper

**Concept ID:** `infotheory-foundation`
**Chapter:** Ch 14 (registry); definition lives in §15.1.3
**Section:** §15.1.3 "Review of Information Theory" (cross-referenced from §14.4.2)
**Pages:** 433-434 (book); PDF pages 449-450
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim)

Bach defines KL divergence first in the discrete setting (§15.1.3,
p.433):

> **KL divergence.** Given two distributions on Z, p and q (which are
> nonnegative functions on Z that sum to 1), then the KL divergence is
> defined as
>
>     D_KL(p‖q)  =  ∑_{z ∈ Z}  p(z) · log( p(z) / q(z) ).
>
> The KL divergence is always nonnegative by convexity of the function
> t ↦ t log t, and equal to zero if and only if p = q. It is a
> classical dissimilarity measure for probability distributions that
> is jointly convex in (p, q).¹ Note that it can also be seen as a
> Bregman divergence (see section 11.1.3).

¹ See more properties in https://en.wikipedia.org/wiki/Kullback-Leibler_divergence.

Bach then extends to continuous laws (§15.1.3, p.434, "From discrete to continuous distributions"):

> Many of the information theory concepts can be extended to continuous
> random variables on R^d by replacing the probability mass function
> with the probability density with respect to a base measure. Then,
> many properties (which were obtained through convex arguments)
> extend when z is continuous-valued, especially the data-processing
> inequality and Fano's inequality (see more details in Cover and
> Thomas, 1999).
>
> For example, the KL divergence between two distributions can be
> defined as
>
>     D_KL(p‖q)  =  E_p [ log (dp/dq)(x) ],
>
> where dp/dq is the density of p with respect to q. A short calculation
> (left as an exercise) shows that for two Gaussian distributions of
> mean vectors μ₁, μ₂ and equal covariance matrices (with value Σ),
> the KL divergence is equal to ½ (μ₁ − μ₂)ᵀ Σ⁻¹ (μ₁ − μ₂).

## Notes

- The continuous form `D_KL(p‖q) = E_p[ log(dp/dq) ]` is the wrapper
  Mathlib calls `InformationTheory.klDiv` (`MeasureTheory` namespace
  for the Radon-Nikodym derivative).
- Bach treats AC of `p ≪ q` and integrability of `log(dp/dq)` implicitly
  via "left as an exercise"; he does not write the `∞` value explicitly.
  All the `kl-*-iff` / `kl-*-of-not-ac` lemmas in the registry are
  housekeeping facts implicit in the Mathlib `klDiv` convention.
- Bach uses this definition only in §14.4.2 (PAC-Bayes) and §15.1.4
  (Fano + information-theoretic lower bounds). For the wiki, this is
  the F5 foundation concept that downstream `pac-bayes-*` concepts
  build on.
- Bach does not state KL = ∞ explicitly anywhere — these are Mathlib
  conventions for handling non-AC measures and non-integrable
  Radon-Nikodym derivatives. See `kl-of-not-ac`, `kl-zero-right`,
  `kl-eq-top-iff`, `kl-ne-top-iff` excerpts.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`kl-eq-top-iff`](./kl-eq-top-iff.md) — KL = ∞ iff non-AC or non-integrable
- [`kl-ne-top-iff`](./kl-ne-top-iff.md) — KL ≠ ∞ iff absolutely continuous and integrable
- [`kl-of-not-ac`](./kl-of-not-ac.md) — KL divergence is ∞ when not absolutely continuous
- [`kl-zero-right`](./kl-zero-right.md) — KL with zero right measure is ∞
- [`markov-inequality`](./markov-inequality.md) — Markov's inequality (real probabilistic statement)
- [`pac-bayes-kl`](./pac-bayes-kl.md) — PAC-Bayes KL divergence wrapper
- [`pinsker-bretagnolle-huber`](./pinsker-bretagnolle-huber.md) — Pinsker / Bretagnolle–Huber inequality (algebraic core anchor)
- [`testing-error-nonneg`](./testing-error-nonneg.md) — Statistical lower-bound anchor: testing error nonneg

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/InfoTheory.lean`
- **Theorem/def name:** `kl`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

