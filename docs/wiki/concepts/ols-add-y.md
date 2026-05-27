# OLS linear in labels

**ID:** `ols-add-y`  
**Chapter:** Ch03 (Bach §3.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `OLS`

## Statement

_See textbook excerpt below or [`tasks/ols-add-y/`](../../../tasks/ols-add-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — OLS linear in labels

**Concept ID:** `ols-add-y`
**Chapter:** Ch 3
**Section:** 3.3 (Ordinary Least-Squares Estimator)
**Pages:** 47–48
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state additivity-in-`y` of the OLS estimator as a named
proposition; it is an immediate algebraic corollary of Proposition 3.1.
The closed-form formula (Proposition 3.1, p. 47) reads:

> **Proposition 3.1.** When `Φ` has full column rank, the OLS estimator
> exists and is unique. It is given by
>
>     θ̂ = (ΦᵀΦ)⁻¹ Φᵀ y.

Since `y ↦ (ΦᵀΦ)⁻¹ Φᵀ y` is a linear map in the response vector `y`, we
have additivity:

```
olsEstimator(Φ, y₁ + y₂) = olsEstimator(Φ, y₁) + olsEstimator(Φ, y₂).
```

## Proof (verbatim)

Bach gives no separate proof — additivity in `y` is immediate from the
closed-form expression `θ̂ = (ΦᵀΦ)⁻¹ Φᵀ y`, which is linear in `y`.

Bach's derivation of the closed form (p. 47–48), which we cite as the
upstream proof:

> *Proof.* Since the function `R̂` is coercive (i.e., going to infinity at
> infinity) and continuous, it admits at least a minimizer. Moreover, it
> is differentiable, so a minimizer `θ̂` must satisfy `R̂'(θ̂) = 0` where
> `R̂'(θ) ∈ ℝᵈ` is the gradient of `R̂` at `θ`. For all `θ ∈ ℝᵈ`, we get,
> by expanding the square and computing the gradient:
>
>     R̂(θ) = (1/n)(‖y‖² − 2θᵀΦᵀy + θᵀΦᵀΦθ),
>     R̂'(θ) = (2/n)(ΦᵀΦθ − Φᵀy).
>
> The condition `R̂'(θ̂) = 0` gives the so-called **normal equation**:
>
>     ΦᵀΦ θ̂ = Φᵀ y.
>
> The multidimensional linear normal equations has a unique solution:
> `θ̂ = (ΦᵀΦ)⁻¹ Φᵀ y`. This shows the uniqueness of the minimizer of
> `R̂`, as well as its closed-form expression.

## Notes

- This is a structural corollary of Proposition 3.1: the map
  `y ↦ (ΦᵀΦ)⁻¹ Φᵀ y` is linear, so it is additive over `y₁ + y₂`.
- The Lean proof in `LTFP/Ch03_LinearLeastSquares/OLS.lean#olsEstimator_add_y`
  unfolds the definition and uses `Matrix.mulVec_add`.
- Bach does not flag this lemma; it is added in LTFP-Lean for downstream
  algebraic manipulations (e.g., Ridge-OLS reductions, debiasing).

## Prerequisites (Bach's dependency graph)

- [`ols-closed-form`](./ols-closed-form.md) — OLS closed form: β̂ = (XᵀX)⁻¹Xᵀy

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/OLS.lean`
- **Theorem/def name:** `olsEstimator_add_y`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

