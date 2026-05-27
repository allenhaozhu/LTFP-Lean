# Estimation error: predictor risk − best-in-class risk

**ID:** `estimation-error`  
**Chapter:** Ch04 (Bach §4.4, p. 85)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/estimation-error/`](../../../tasks/estimation-error/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Estimation error

**Concept ID:** `estimation-error`
**Chapter:** Ch 4
**Section:** 4.4
**Pages:** 85-86
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
The estimation error is the gap between the risk of the chosen predictor f̂ and the best
in-class risk:

$$\text{estimation error} = R(\hat f) - \inf_{f \in F} R(f).$$

Setting g_F ∈ arg min_{g ∈ F} R(g) and f̂ ∈ arg min_{f ∈ F} R̂(f), Bach decomposes:

$$R(\hat f) - \inf_{f \in F} R(f) = R(\hat f) - R(g_F)
= \big(R(\hat f) - \hat R(\hat f)\big) + \big(\hat R(\hat f) - \hat R(g_F)\big) + \big(\hat R(g_F) - R(g_F)\big)$$
$$\le \sup_{f\in F}\big(R(f)-\hat R(f)\big) + 0 + \sup_{f\in F}\big(\hat R(f)-R(f)\big), \qquad (4.10)$$

by definition of f̂ (the middle term ≤ 0). "This is often further upper-bounded by
2 sup_{f∈F} |R̂(f) − R(f)|."

## Proof (verbatim)
"The estimation error is often decomposed using g_F ∈ arg min_{g∈F} R(g) as the minimizer of
the expected risk for our class of models and f̂ ∈ arg min_{f∈F} R̂(f) as the minimizer of
the empirical risk:

R(f̂) − inf_{f∈F} R(f) = R(f̂) − R(g_F)
                       = R(f̂) − R̂(f̂) + R̂(f̂) − R̂(g_F) + R̂(g_F) − R(g_F)
                       ≤ sup_{f∈F} (R(f) − R̂(f)) + R̂(f̂) − R̂(g_F) + sup_{f∈F} (R̂(f) − R(f))
                       ≤ sup_{f∈F} (R(f) − R̂(f)) + 0 + sup_{f∈F} (R̂(f) − R(f))
                          by definition of f̂. (4.10)"

The factor of 2 in 2 sup_f |R(f) − R̂(f)| comes from absorbing both directional suprema.

## Notes
- Decomposes via R̂ telescoping; key reduction is "ERM gives R̂(f̂) − R̂(g_F) ≤ 0".
- Reduces estimation-error control to uniform deviation control |R − R̂| over F.
- Random quantity (depends on data); decays in n.
- When f̂ is only an ε-approximate ERM, an extra +ε optimization-error term appears.

## Prerequisites (Bach's dependency graph)

- [`population-risk`](./population-risk.md) — Population risk R(f) = E[ℓ(f(x), y)]

## Dependents (concepts that use this)

- [`estim-error-self-anchor`](./estim-error-self-anchor.md) — Estimation error of fhat against itself = 0
- [`excess-risk-decomposition`](./excess-risk-decomposition.md) — Excess risk = approximation + estimation

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/RiskDecomposition.lean`
- **Theorem/def name:** `estimationError`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

