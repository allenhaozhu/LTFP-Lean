# Ridge subtracts in labels

**ID:** `ridge-sub-y`  
**Chapter:** Ch03 (Bach §3.6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Ridge`

## Statement

_See textbook excerpt below or [`tasks/ridge-sub-y/`](../../../tasks/ridge-sub-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Ridge subtracts in labels

**Concept ID:** `ridge-sub-y`
**Chapter:** Ch 3
**Section:** 3.6 (Ridge Least-Squares Regression)
**Pages:** 56–57
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state subtraction-in-`y` of the ridge estimator as a named
proposition; it follows immediately from Proposition 3.6 (p. 57):

> **Proposition 3.6.** Recall `Σ̂ = (1/n) ΦᵀΦ ∈ ℝᵈˣᵈ`. We have
>
>     θ̂_λ = (1/n) (Σ̂ + λI)⁻¹ Φᵀ y.

Since `y ↦ (1/n)(Σ̂ + λI)⁻¹ Φᵀ y` is a linear map in `y`, it commutes
with subtraction:

```
ridgeEstimator(Φ, y₁ − y₂, λ)
    = ridgeEstimator(Φ, y₁, λ) − ridgeEstimator(Φ, y₂, λ).
```

## Proof (verbatim)

Bach gives no separate proof. From the closed-form expression
`θ̂_λ = (ΦᵀΦ + nλI)⁻¹ Φᵀ y`, which is ℝ-linear in `y`:

`(ΦᵀΦ + nλI)⁻¹ Φᵀ (y₁ − y₂) = (ΦᵀΦ + nλI)⁻¹ Φᵀ y₁ − (ΦᵀΦ + nλI)⁻¹ Φᵀ y₂`.

The underlying closed-form derivation (Bach, pp. 56–57):

> *Proof.* As with the proof of Proposition 3.1, we can compute the
> gradient of the objective function, which is equal to
> `(2/n)(ΦᵀΦθ − Φᵀy) + 2λθ`. Setting it to zero leads to the estimator.
> Note that when `λ > 0`, the linear system always has a unique solution
> regardless of the invertibility of `Σ̂`.

## Notes

- Subtraction-in-`y` is a structural corollary of Proposition 3.6.
- The Lean proof at
  `LTFP/Ch03_LinearLeastSquares/Ridge.lean#ridgeEstimator_sub` reduces
  to `Matrix.mulVec_sub` after unfolding the closed form.
- Bach does not flag this lemma; it is added in LTFP-Lean to support
  residual-vs-mean decompositions and shift-invariance arguments.

## Prerequisites (Bach's dependency graph)

- [`ridge-closed-form`](./ridge-closed-form.md) — Ridge closed form: β̂_λ = (XᵀX + nλI)⁻¹Xᵀy

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/Ridge.lean`
- **Theorem/def name:** `ridgeEstimator_sub`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

