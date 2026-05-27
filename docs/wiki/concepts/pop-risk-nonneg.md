# populationRisk of nonneg loss is nonneg

**ID:** `pop-risk-nonneg`  
**Chapter:** Ch02 (Bach §2.2.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/pop-risk-nonneg/`](../../../tasks/pop-risk-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — populationRisk of nonneg loss is nonneg

**Concept ID:** `pop-risk-nonneg`
**Chapter:** Ch 2
**Section:** 2.2.2 (Risks)
**Pages:** 25, 27
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach frames losses as taking values in `R+` "often" (§2.2.1, p. 25). For
any nonneg-valued loss `ℓ : Y × Y → R+`, the expected risk
`R(f) = E[ℓ(y, f(x))]` is also nonneg.

Formally:

> If `ℓ(y, z) ≥ 0` for all `y, z`, then `R(f) ≥ 0`.

This is **monotonicity of the integral** applied to the pointwise inequality
`ℓ(y, f(x)) ≥ 0`.

## Proof (verbatim)

Bach does not prove this; he uses it implicitly when arguing `R∗ ≥ 0`
(Bayes risk is nonneg, p. 28) and `R(f) − R∗ ≥ 0` (excess risk is nonneg,
Definition 2.3, p. 29).

In Mathlib: `MeasureTheory.integral_nonneg` applied to `fun xy => ℓ xy.2 (f xy.1)`.

## Notes

- Follows from `pop-risk-eq-integral` + `MeasureTheory.integral_nonneg`.
- Foundational: `bayes-risk-nonneg`, `excess-risk-nonneg`, and most
  generalization bounds chain off this fact.
- Discharged in Lean by:
  ```
  refine MeasureTheory.integral_nonneg ?_
  intro xy
  exact hℓ_nonneg _ _
  ```

## Prerequisites (Bach's dependency graph)

- [`expectation-nonneg`](./expectation-nonneg.md) — Expectation of nonneg function is nonneg
- [`population-risk`](./population-risk.md) — Population risk R(f) = E[ℓ(f(x), y)]

## Dependents (concepts that use this)

- [`bayes-risk-nonneg`](./bayes-risk-nonneg.md) — Bayes risk is nonneg under nonneg loss

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `populationRisk_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

