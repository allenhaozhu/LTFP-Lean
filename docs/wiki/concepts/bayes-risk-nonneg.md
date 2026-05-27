# Bayes risk is nonneg under nonneg loss

**ID:** `bayes-risk-nonneg`  
**Chapter:** Ch02 (Bach §2.2.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Bayes-risk`

## Statement

_See textbook excerpt below or [`tasks/bayes-risk-nonneg/`](../../../tasks/bayes-risk-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bayes risk is nonneg under nonneg loss

**Concept ID:** `bayes-risk-nonneg`
**Chapter:** Ch 2
**Section:** 2.2.3 (Bayes Risk and Bayes Predictor)
**Pages:** 28
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Within Proposition 2.1 (p. 28), Bach defines:

>     R∗ = E_{x' ∼ p}[ inf_{z ∈ Y} E[ℓ(y, z) | x = x'] ].

If `ℓ ≥ 0` pointwise, then `inf_z E[ℓ(y, z) | x = x'] ≥ 0` (an inf of
nonneg numbers is nonneg, or `≥ 0` by extension when the set is empty), and
therefore `R∗ ≥ 0` by monotonicity of expectation.

Bach comments (p. 29):

> (2) the Bayes risk is usually nonzero (unless the dependence between `x`
> and `y` is deterministic).

i.e., the Bayes risk is `≥ 0` always, and `> 0` unless the labeling is
deterministic.

## Proof (verbatim)

Not proved explicitly; immediate from `R∗ = E[inf_z r(z | x)]`,
`r(z | x) = E[ℓ(y, z) | x] ≥ 0` (conditional expectation of a nonneg variable
is nonneg), and monotonicity of expectation.

## Notes

- Chains from `pop-risk-nonneg` if we adopt the equivalent definition
  `R∗ = inf_f R(f)` — then `R∗ ≥ inf_f 0 = 0` (or directly from the integral
  form).
- Necessary structural lemma for `excess-risk-nonneg` to be a meaningful
  statement (otherwise `R(f) − R∗` could be unbounded below in pathological
  cases).
- One-line in Lean via `inf_nonneg` + `integral_nonneg`.

## Prerequisites (Bach's dependency graph)

- [`bayes-risk-minimum`](./bayes-risk-minimum.md) — Bayes risk equals the infimum of population risk
- [`pop-risk-nonneg`](./pop-risk-nonneg.md) — populationRisk of nonneg loss is nonneg

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `bayesRisk_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

