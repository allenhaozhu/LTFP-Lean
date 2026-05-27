# PAC-Bayes KL = ∞ when posterior not absolutely continuous

**ID:** `pac-bayes-kl-not-ac`  
**Chapter:** Ch14 (Bach §14.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `PAC-Bayes`, `KL-divergence`

## Statement

_See textbook excerpt below or [`tasks/pac-bayes-kl-not-ac/`](../../../tasks/pac-bayes-kl-not-ac/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — PAC-Bayes KL = ∞ when posterior not AC w.r.t. prior

**Concept ID:** `pac-bayes-kl-not-ac`
**Chapter:** Ch 14
**Section:** §14.4.2 (PAC-Bayes uses KL); not stated explicitly by Bach
**Pages:** 424 (book); PDF page 440
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim — Bach treats AC implicitly)

Bach's PAC-Bayes section assumes `ρ ≪ q` whenever the bound is invoked
(otherwise the bound's RHS is vacuous, equal to ∞). He writes (§14.4.2,
p.424):

> D(ρ‖q)  =  ∫_Θ  log( dρ/dq )(θ) · dρ(θ).

The case `ρ ⊄ q ⇒ D(ρ‖q) = ∞` is Mathlib's convention for
`InformationTheory.klDiv` applied to the (posterior, prior) pair.

## Notes

- Bach does not state this case. The lemma is a direct corollary of
  `kl-of-not-ac` specialized to the PAC-Bayes (posterior, prior) order.
- Operationally: when the posterior `ρ` puts mass on parameters that
  the prior `q` assigns zero density to, the bound's complexity term
  is ∞, so the bound is uninformative for that `ρ`. This is the
  expected behavior — the prior must "cover" the posterior for the
  bound to be useful.
- Lean discharge is `simp [pacBayesKL, klDiv, ...]` once the underlying
  `kl-of-not-ac` is in scope.

## Prerequisites (Bach's dependency graph)

- [`kl-of-not-ac`](./kl-of-not-ac.md) — KL divergence is ∞ when not absolutely continuous
- [`pac-bayes-kl`](./pac-bayes-kl.md) — PAC-Bayes KL divergence wrapper

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/PACBayes.lean`
- **Theorem/def name:** `pacBayesKL_of_not_ac`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

