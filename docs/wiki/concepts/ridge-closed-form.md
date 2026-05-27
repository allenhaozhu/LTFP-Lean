# Ridge closed form: β̂_λ = (XᵀX + nλI)⁻¹Xᵀy

**ID:** `ridge-closed-form`  
**Chapter:** Ch03 (Bach §3.6, p. 56)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Ridge`

## Statement

_See textbook excerpt below or [`tasks/ridge-closed-form/`](../../../tasks/ridge-closed-form/) if available._

## Bach's textbook treatment

# Book excerpt — `ridge-closed-form` (Bach 2024 §3.6, p. 56)

> Ridge regression solves the regularized empirical risk
>
>     R̂_λ(θ) = (1/n) ‖y − Φ θ‖² + λ ‖θ‖².
>
> The gradient `R̂_λ'(θ) = (2/n)(ΦᵀΦ θ − Φᵀ y) + 2 λ θ` vanishes
> exactly when
>
>     (ΦᵀΦ + n λ I) θ = Φᵀ y          (the regularized normal equation).
>
> When `λ > 0`, `ΦᵀΦ + n λ I` is positive-definite (hence invertible),
> so the unique solution is the ridge estimator
>
>     θ̂_λ = (ΦᵀΦ + n λ I)⁻¹ Φᵀ y.
>
> Crucially, no rank assumption on `Φ` is required: regularization
> alone makes the matrix invertible.

## Lean target

The file `LTFP/Ch03_LinearLeastSquares/Ridge.lean` already defines

    noncomputable def ridgeEstimator
        (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (lam : ℝ) : Fin d → ℝ :=
      ((Xᵀ * X + (n * lam) • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ * Xᵀ).mulVec y

The theorem is the **regularized normal equation**:

    theorem ridge_closed_form {n d : ℕ}
        (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (lam : ℝ)
        (hX : IsUnit
              (Xᵀ * X + (n * lam) • (1 : Matrix (Fin d) (Fin d) ℝ)).det) :
        (Xᵀ * X + (n * lam) • (1 : Matrix (Fin d) (Fin d) ℝ))
            *ᵥ ridgeEstimator X y lam = Xᵀ *ᵥ y

Proof sketch (one-liner): unfold `ridgeEstimator`, then rewrite via
`Matrix.mulVec_mulVec` and `Matrix.mul_nonsing_inv_cancel_left` —
exactly the same pattern used for `ols_closed_form`.

## Acceptable smaller fallback

If the full statement gets stuck, fall back to the matrix-equation
form (no `mulVec`):

    theorem ridge_closed_form {n d : ℕ}
        (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (lam : ℝ)
        (hX : IsUnit
              (Xᵀ * X + (n * lam) • (1 : Matrix (Fin d) (Fin d) ℝ)).det) :
        (Xᵀ * X + (n * lam) • (1 : Matrix (Fin d) (Fin d) ℝ))
          * ((Xᵀ * X + (n * lam) • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹
              * Xᵀ) = Xᵀ

via `Matrix.mul_nonsing_inv_cancel_left`.

**No `sorry`, no `admit`, no `True`** — pick whichever lands cleanly.
Useful Mathlib lemmas: `Matrix.mul_nonsing_inv_cancel_left`,
`Matrix.mulVec_mulVec`, `Matrix.mul_assoc`, `Matrix.one_mulVec`.

## Prerequisites (Bach's dependency graph)

- [`ols-closed-form`](./ols-closed-form.md) — OLS closed form: β̂ = (XᵀX)⁻¹Xᵀy

## Dependents (concepts that use this)

- [`krr-coeffs`](./krr-coeffs.md) — Kernel ridge regression coefficient α̂_λ = (K + nλI)⁻¹ y
- [`ridge-bias-variance`](./ridge-bias-variance.md) — Ridge bias-variance trade-off (fixed design)
- [`ridge-smul-y`](./ridge-smul-y.md) — Ridge homogeneous in labels
- [`ridge-sub-y`](./ridge-sub-y.md) — Ridge subtracts in labels
- [`ridge-zero-y`](./ridge-zero-y.md) — Ridge with zero labels = 0

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/Ridge.lean`
- **Theorem/def name:** `ridge_closed_form`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

