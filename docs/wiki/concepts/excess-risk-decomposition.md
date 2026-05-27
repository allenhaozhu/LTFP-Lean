# Excess risk = approximation + estimation

**ID:** `excess-risk-decomposition`  
**Chapter:** Ch04 (Bach §4.2, p. 84)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/excess-risk-decomposition/`](../../../tasks/excess-risk-decomposition/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Excess risk = approximation + estimation

**Concept ID:** `excess-risk-decomposition`
**Chapter:** Ch 4
**Section:** 4.2
**Pages:** 84
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
**Risk Minimization Decomposition.** For a family F of prediction functions f : X → R and
the empirical risk minimizer f̂ ∈ arg min_{f ∈ F} R̂(f), the excess risk decomposes as

$$R(\hat f) - R^* = \big\{R(\hat f) - \inf_{f' \in F} R(f')\big\} + \big\{\inf_{f' \in F} R(f') - R^*\big\}$$
$$= \text{estimation error} + \text{approximation error}.$$

## Proof (verbatim)
"We now consider a family F of prediction functions f : X → R. Empirical risk minimization
aims to compute
                       f̂ ∈ arg min_{f ∈ F} R̂(f) = (1/n) Σ_{i=1}^n ℓ(y_i, f(x_i))

with algorithms presented in chapter 5. We consider loss functions that are defined for
real-valued outputs even for binary classification problems through the use of surrogates
presented in section 4.1.1.

We can decompose the risk into two terms as follows:

R(f̂) − R^* = { R(f̂) − inf_{f' ∈ F} R(f') } + { inf_{f' ∈ F} R(f') − R^* }
            = estimation error + approximation error."

## Notes
- Trivially identical: simply telescoping through inf_{f' ∈ F} R(f').
- Splits a generalization analysis into (a) modeling capacity question (approximation)
  and (b) statistical convergence question (estimation).
- Approximation: deterministic, larger F ⇒ smaller; estimation: random, larger F ⇒ larger.
- This drives chapters 4-9's overall narrative (bias-variance tradeoff in supervised learning).

## Prerequisites (Bach's dependency graph)

- [`approximation-error`](./approximation-error.md) — Approximation error: best-in-class − Bayes risk
- [`estimation-error`](./estimation-error.md) — Estimation error: predictor risk − best-in-class risk

## Dependents (concepts that use this)

- [`excess-risk-eq-approx-when-optimal`](./excess-risk-eq-approx-when-optimal.md) — Optimal predictor in H ⇒ excess risk = approximation error
- [`excess-risk-telescope`](./excess-risk-telescope.md) — Excess risk telescope: a-c = (a-b)+(b-c)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/RiskDecomposition.lean`
- **Theorem/def name:** `excess_risk_decomposition`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

