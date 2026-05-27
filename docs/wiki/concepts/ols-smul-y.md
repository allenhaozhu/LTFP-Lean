# OLS homogeneous in labels

**ID:** `ols-smul-y`  
**Chapter:** Ch03 (Bach §3.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `OLS`

## Statement

_See textbook excerpt below or [`tasks/ols-smul-y/`](../../../tasks/ols-smul-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — OLS homogeneous in labels

**Concept ID:** `ols-smul-y`
**Chapter:** Ch 3
**Section:** 3.3 (Ordinary Least-Squares Estimator)
**Pages:** 47–48
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state scalar-homogeneity of the OLS estimator as a named
proposition; it follows immediately from Proposition 3.1 (p. 47):

> **Proposition 3.1.** When `Φ` has full column rank, the OLS estimator
> exists and is unique. It is given by
>
>     θ̂ = (ΦᵀΦ)⁻¹ Φᵀ y.

Since `y ↦ (ΦᵀΦ)⁻¹ Φᵀ y` is a linear map in the response vector `y`, for
any scalar `c ∈ ℝ`:

```
olsEstimator(Φ, c · y) = c · olsEstimator(Φ, y).
```

## Proof (verbatim)

Bach gives no separate proof — homogeneity in `y` is immediate from the
closed-form expression `θ̂ = (ΦᵀΦ)⁻¹ Φᵀ y`, which is linear in `y`.

The derivation of the closed form (Bach, pp. 47–48):

> *Proof.* `R̂` is coercive, continuous, and differentiable, so any
> minimizer `θ̂` satisfies `R̂'(θ̂) = 0`. Expanding the square gives
> `R̂(θ) = (1/n)(‖y‖² − 2θᵀΦᵀy + θᵀΦᵀΦθ)` and
> `R̂'(θ) = (2/n)(ΦᵀΦθ − Φᵀy)`. Setting `R̂'(θ̂) = 0` yields the **normal
> equation** `ΦᵀΦ θ̂ = Φᵀ y`, whose unique solution is
> `θ̂ = (ΦᵀΦ)⁻¹ Φᵀ y`.

## Notes

- Like additivity, scalar-homogeneity in `y` follows because
  `y ↦ (ΦᵀΦ)⁻¹ Φᵀ y` is a linear map.
- The Lean proof at
  `LTFP/Ch03_LinearLeastSquares/OLS.lean#olsEstimator_smul_y` discharges
  this via `Matrix.mulVec_smul`.
- Combined with `ols-add-y`, this gives full ℝ-linearity of OLS in the
  label vector.
- Bach does not flag this lemma separately; it is added in LTFP-Lean as
  a building block (e.g., to deduce that OLS with zero labels is zero,
  to negate labels, and so on).

## Prerequisites (Bach's dependency graph)

- [`ols-closed-form`](./ols-closed-form.md) — OLS closed form: β̂ = (XᵀX)⁻¹Xᵀy

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/OLS.lean`
- **Theorem/def name:** `olsEstimator_smul_y`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

