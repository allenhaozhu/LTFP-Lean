# PAC-Bayes KL definition unfolded

**ID:** `pacbayes-kl-def`  
**Chapter:** Ch14 (Bach §14.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `PAC-Bayes`, `KL-divergence`

## Statement

_See textbook excerpt below or [`tasks/pacbayes-kl-def/`](../../../tasks/pacbayes-kl-def/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — PAC-Bayes KL definition unfolded

**Concept ID:** `pacbayes-kl-def`
**Chapter:** Ch 14
**Section:** §14.4.2 PAC-Bayes (uses KL definition from §15.1.3)
**Pages:** 424 (book); PDF page 440
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim)

Bach (§14.4.2, p.424), defining the KL used in the PAC-Bayes bound:

> D(ρ‖q)  =  ∫_Θ  log( dρ/dq )(θ) · dρ(θ).

(Cross-reference: Bach §15.1.3, p.434, defines KL in the same form
for general continuous measures: `D_KL(p‖q) = E_p[log(dp/dq)(x)]`.)

The "unfolded" form of the Lean wrapper `pacBayesKL ρ q` should equal
this integral. Equivalently (by Mathlib's `klDiv` definition),
`pacBayesKL ρ q = ∫⁻ θ, ENNReal.ofReal (log (rnDeriv ρ q θ)) ∂ρ` or
`pacBayesKL ρ q = ∫ θ, log (rnDeriv ρ q θ) ∂ρ`, depending on the
Mathlib convention for `ℝ` vs `ℝ≥0∞` typed return.

## Notes

- This is the "rewrite to integral form" lemma. Useful when downstream
  proofs need to manipulate `pacBayesKL` as an integral (e.g., to
  invoke Jensen, monotone convergence, etc.).
- Bach writes `D(ρ‖q)` in the integral form directly; the Lean wrapper
  may hide this behind a Mathlib definition that needs unfolding.
- Discharge: `unfold pacBayesKL klDiv; rfl` or
  `simp [pacBayesKL, klDiv_eq_integral]`.

## Prerequisites (Bach's dependency graph)

- [`pac-bayes-kl`](./pac-bayes-kl.md) — PAC-Bayes KL divergence wrapper

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/PACBayes.lean`
- **Theorem/def name:** `pacBayesKL_def`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

