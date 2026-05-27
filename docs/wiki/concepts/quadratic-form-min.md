# Minimization of a positive-definite quadratic form

**ID:** `quadratic-form-min`  
**Chapter:** Ch01 (Bach §1.1.1, p. 3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/quadratic-form-min/`](../../../tasks/quadratic-form-min/) if available._

## Bach's textbook treatment

# Book excerpt — `quadratic-form-min` (Bach 2024 §1.1.1, pp. 3-4)

> Given a positive-definite (and hence invertible) symmetric matrix
> `A ∈ ℝⁿˣⁿ` and vector `b ∈ ℝⁿ`, the minimization of quadratic forms
> with linear terms can be done in closed form:
>
>   `inf_{x∈ℝⁿ} ½ xᵀ A x − bᵀ x = −½ bᵀ A⁻¹ b`,
>
> with the minimizer `x⋆ = A⁻¹ b` obtained by zeroing the gradient
> `f'(x) = A x − b` of `f(x) = ½ xᵀ A x − bᵀ x`. Moreover,
>
>   `½ xᵀ A x − bᵀ x = ½ (x − x⋆)ᵀ A (x − x⋆) − ½ bᵀ A⁻¹ b`.

## Lean target

The "completing the square" identity above is the cleanest core fact and
the easiest to formalize. Aim for:

    theorem quadratic_form_min {n : ℕ}
        (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ)
        (hA : A.PosDef) :
        (1/2) * (x ⬝ᵥ A.mulVec x) - b ⬝ᵥ x =
          (1/2) * ((x - A⁻¹.mulVec b) ⬝ᵥ A.mulVec (x - A⁻¹.mulVec b))
            - (1/2) * (b ⬝ᵥ A⁻¹.mulVec b)

## Acceptable smaller fallback

If proving the full completing-the-square identity gets unwieldy,
fall back to the value-at-the-minimizer corollary:

    theorem quadratic_form_min {n : ℕ}
        (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
        (hA : A.PosDef) :
        let xstar := A⁻¹.mulVec b
        (1/2) * (xstar ⬝ᵥ A.mulVec xstar) - b ⬝ᵥ xstar =
          - (1/2) * (b ⬝ᵥ A⁻¹.mulVec b)

In either case **no `sorry`, no `admit`** — the body must be a real proof.

The relevant Mathlib namespace is `Matrix`. Useful lemmas:
`Matrix.PosDef.isUnit_det`, `Matrix.mul_inv_cancel`, `Matrix.dotProduct_mulVec`,
`Matrix.mulVec_smul`, `Matrix.PosDef.transpose`. `A` is symmetric (PosDef
implies `A.IsHermitian`), which gives `Aᵀ = A`.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`ols-closed-form`](./ols-closed-form.md) — OLS closed form: β̂ = (XᵀX)⁻¹Xᵀy
- [`pos-def-isunit`](./pos-def-isunit.md) — Positive-definite matrix is invertible

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch01_Preliminaries/LinAlg.lean`
- **Theorem/def name:** `quadratic_form_min`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

