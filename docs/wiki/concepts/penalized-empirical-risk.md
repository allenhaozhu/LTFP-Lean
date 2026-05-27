# Penalized empirical risk for SRM (♦)

**ID:** `penalized-empirical-risk`  
**Chapter:** Ch04 (Bach §4.6.1, p. 104)  
**Kind:** definition  
**Difficulty:** diamond  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/penalized-empirical-risk/`](../../../tasks/penalized-empirical-risk/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Penalized empirical risk for SRM

**Concept ID:** `penalized-empirical-risk`
**Chapter:** Ch 4
**Section:** 4.6.1 (also 4.5.5 for the L²-penalized version)
**Pages:** 100, 103-104
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
The penalized empirical risk (with penalty / regularizer Ω and weight λ ≥ 0) is

$$\hat R_\lambda(\theta) = \hat R(\theta) + \lambda \Omega(\theta) = \frac{1}{n}\sum_{i=1}^n \ell(y_i, \theta^\top \varphi(x_i)) + \lambda \Omega(\theta), \qquad (4.19)$$

with squared-L^2 special case:
$$\hat R(\theta) + \tfrac{\lambda}{2}\|\theta\|_2^2 = \hat R(f_\theta) + \tfrac{\lambda}{2}\|\theta\|_2^2. \qquad (4.17)$$

**Structural risk minimization** chooses a model index by minimizing a penalized data-dependent
generalization bound:

$$\hat\imath \in \arg\min_{i \in \{1,\dots,m\}} \Big\{\hat R(\hat f_i) + 2 R_n(H_i) + \tfrac{\ell_\infty}{\sqrt{2n}}\sqrt{\log(1/\pi_i)}\Big\}, \qquad (4.24)$$

with weights π_1, …, π_m summing to 1.

## Proof (verbatim)
"In practice, it is preferable to penalize by the norm Ω(θ) instead of constraining. While
the respective sets of solutions when letting the respective constraint and regularization
parameters vary are the same, the main reason is that the hyperparameter is easier to find,
and the optimization is typically easier."

For SRM (4.6.1): "We minimize the data-dependent generalization bounds plus an additional
parameter to take into account the prior on models." Combined with eq. (4.23) for each model
and a union bound (πᵢδ replacing δ), Bach concludes with probability ≥ 1 − δ,

R(f̂_{î}) ≤ min_i [ inf_{fᵢ ∈ Fᵢ} R(fᵢ) + 4 R_n(Hᵢ) + 2(ℓ_∞/√(2n))√log(1/πᵢ) + 2(ℓ_∞/√(2n))√log(2/δ) ]. (4.25)

## Notes
- Penalty is convex in θ when Ω is a norm; squared L^2 (4.17) is strongly convex.
- ♦ (diamond) marker: a more advanced section in Bach's notation.
- SRM combines an in-class regularization choice with a model-index choice via π_i prior weights.
- Penalized risk = empirical risk on penalty = 0; additive when penalty is summed (`penalized-add-pen`).

## Prerequisites (Bach's dependency graph)

- [`empirical-risk`](./empirical-risk.md) — Empirical risk R̂_n(f)

## Dependents (concepts that use this)

- [`penalized-add-pen`](./penalized-add-pen.md) — Penalized risk additive in penalty
- [`penalized-zero-pen`](./penalized-zero-pen.md) — Penalized risk with zero penalty = empirical risk

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/ModelSelection.lean`
- **Theorem/def name:** `penalizedEmpiricalRisk`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

