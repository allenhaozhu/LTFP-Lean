# Ridge with zero labels = 0

**ID:** `ridge-zero-y`  
**Chapter:** Ch03 (Bach §3.6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Ridge`

## Statement

_See textbook excerpt below or [`tasks/ridge-zero-y/`](../../../tasks/ridge-zero-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Ridge with zero labels = 0

**Concept ID:** `ridge-zero-y`
**Chapter:** Ch 3
**Section:** 3.6 (Ridge Least-Squares Regression)
**Pages:** 56–57
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state the "zero-label ⇒ zero-estimator" corollary
explicitly; it follows immediately from the closed-form expression of
the ridge least-squares estimator.

> **Definition 3.2 (Ridge least-squares regression estimator).** For a
> regularization parameter `λ > 0`, the ridge least-squares estimator
> `θ̂_λ` is the minimizer of
>
>     min_{θ ∈ ℝᵈ}  (1/n) ‖y − Φθ‖² + λ‖θ‖².
>
> **Proposition 3.6.** Recall `Σ̂ = (1/n) ΦᵀΦ ∈ ℝᵈˣᵈ`. We have
>
>     θ̂_λ = (1/n) (Σ̂ + λI)⁻¹ Φᵀ y     [equivalently  (ΦᵀΦ + nλI)⁻¹ Φᵀ y].

For `y = 0`, the right-hand side becomes
`(1/n)(Σ̂ + λI)⁻¹ Φᵀ · 0 = 0`. Hence:

```
ridgeEstimator(Φ, 0, λ) = 0.
```

## Proof (verbatim)

Bach gives no separate proof. The closed-form derivation (Bach, pp. 56–57):

> *Proof.* As with the proof of Proposition 3.1, we can compute the
> gradient of the objective function, which is equal to
> `(2/n)(ΦᵀΦθ − Φᵀy) + 2λθ`. Setting it to zero leads to the estimator.
> Note that when `λ > 0`, the linear system always has a unique solution
> regardless of the invertibility of `Σ̂`.

For `y = 0`, the normal-equation right-hand side is `Φᵀ · 0 = 0`, so the
unique solution of `(ΦᵀΦ + nλI) θ = 0` is `θ = 0`.

## Notes

- This is the `y = 0` specialization of Proposition 3.6 — Ridge is
  linear in `y`, so it sends `0` to `0`.
- The Lean proof at
  `LTFP/Ch03_LinearLeastSquares/Ridge.lean#ridgeEstimator_zero`
  unfolds the definition and uses `Matrix.mulVec_zero` plus
  `(Σ̂ + λI)⁻¹ · 0 = 0`.
- Bach does not flag this corollary; it is added in LTFP-Lean as a
  building block for ridge linearity/homogeneity lemmas.

## Prerequisites (Bach's dependency graph)

- [`ridge-closed-form`](./ridge-closed-form.md) — Ridge closed form: β̂_λ = (XᵀX + nλI)⁻¹Xᵀy

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/Ridge.lean`
- **Theorem/def name:** `ridgeEstimator_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

