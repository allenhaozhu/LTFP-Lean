# Optimal predictor in H ⇒ excess risk = approximation error

**ID:** `excess-risk-eq-approx-when-optimal`  
**Chapter:** Ch04 (Bach §4.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/excess-risk-eq-approx-when-optimal/`](../../../tasks/excess-risk-eq-approx-when-optimal/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Optimal predictor in H ⇒ excess risk = approximation error

**Concept ID:** `excess-risk-eq-approx-when-optimal`
**Chapter:** Ch 4
**Section:** 4.2 / 4.3
**Pages:** 84-85
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
If f̂ attains the in-class infimum (i.e. R(f̂) = inf_{f ∈ F} R(f), so estimation error = 0),
then the excess risk equals the approximation error:
$$R(\hat f) - R^* = 0 + \big(\inf_{f \in F} R(f) - R^*\big) = \text{approximation error}.$$

## Proof (verbatim)
Direct substitution into the excess-risk decomposition (4.10):
R(f̂) − R^* = { R(f̂) − inf R(f) } + { inf R(f) − R^* } = 0 + approx error = approx error. □

Bach's narrative emphasis is the converse limit (4.3, p. 84-85): "the larger the class, the
smaller the approximation error" — pushing estimation toward 0 leaves only approximation.

## Notes
- Trivial consequence of the additive decomposition (`excess-risk-decomposition` /
  `excess-risk-telescope`).
- Captures the limiting regime: with an estimator that is optimal in F, excess risk is
  exactly the approximation gap.
- Pedagogical: motivates "larger class F" as the only way to reduce excess risk when the
  estimation step is already optimal.

## Prerequisites (Bach's dependency graph)

- [`approximation-error`](./approximation-error.md) — Approximation error: best-in-class − Bayes risk
- [`excess-risk-decomposition`](./excess-risk-decomposition.md) — Excess risk = approximation + estimation

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/RiskDecomposition.lean`
- **Theorem/def name:** `excess_risk_eq_approx_when_optimal`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

