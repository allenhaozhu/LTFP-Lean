# OLS as orthogonal projection onto col(X)

**ID:** `ols-geometric`  
**Chapter:** Ch03 (Bach §3.3.2, p. 48)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** partial  
**Vendored status:** new  
**Topic tags:** `OLS`

## Statement

_See textbook excerpt below or [`tasks/ols-geometric/`](../../../tasks/ols-geometric/) if available._

## Bach's textbook treatment

# Book excerpt — `ols-geometric` (Bach 2024 §3.3.2, p. 48)

> **Proposition 3.2.** The vector of predictions `Φ θ̂ = Φ (ΦᵀΦ)⁻¹ Φᵀ y`
> is the orthogonal projection of `y ∈ ℝⁿ` onto `im(Φ) ⊂ ℝⁿ`, the
> column space of `Φ`.
>
> *Proof.* Let `Π = Φ (ΦᵀΦ)⁻¹ Φᵀ ∈ ℝⁿˣⁿ`. We show `Π` is the
> orthogonal projection onto `im(Φ)`:
> - For any `a ∈ ℝᵈ`: `Π Φ a = Φ (ΦᵀΦ)⁻¹ Φᵀ Φ a = Φ a`. So `Π u = u`
>   for all `u ∈ im(Φ)`.
> - Also, `im(Φ)⊥ = null(Φᵀ)`, so for any `u' ∈ im(Φ)⊥`,
>   `Φᵀ u' = 0`, and hence `Π u' = 0`.

## Lean target

The cleanest core fact and the easiest to formalize is the
**fixed-point** property of the projection on `im(Φ)`:

    theorem ols_is_projection {n d : ℕ}
        (X : Matrix (Fin n) (Fin d) ℝ) (a : Fin d → ℝ)
        (hX : IsUnit (Xᵀ * X).det) :
        (X * (Xᵀ * X)⁻¹ * Xᵀ) *ᵥ (X *ᵥ a) = X *ᵥ a

Proof sketch (one-liner): pull the leftmost `X` outside, then the
inner expression `(Xᵀ * X)⁻¹ * Xᵀ * X = 1` by
`Matrix.nonsing_inv_mul`. Apply `Matrix.mulVec_mulVec`,
`Matrix.mul_assoc`, `Matrix.one_mulVec`.

## Acceptable smaller fallback

If the full statement above gets stuck, fall back to the simpler
fact (the same identity stated as a matrix equation, no `mulVec`):

    theorem ols_is_projection {n d : ℕ}
        (X : Matrix (Fin n) (Fin d) ℝ)
        (hX : IsUnit (Xᵀ * X).det) :
        X * (Xᵀ * X)⁻¹ * Xᵀ * X = X

This is just `Matrix.mul_nonsing_inv_cancel_left`-style algebra.

**No `sorry`, no `admit`, no `True`** — pick whichever lands cleanly.
Useful Mathlib lemmas: `Matrix.nonsing_inv_mul`,
`Matrix.mul_nonsing_inv`, `Matrix.mul_assoc`, `Matrix.mulVec_mulVec`,
`Matrix.one_mulVec`.

## Prerequisites (Bach's dependency graph)

- [`ols-closed-form`](./ols-closed-form.md) — OLS closed form: β̂ = (XᵀX)⁻¹Xᵀy

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = partial`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/OLS.lean`
- **Theorem/def name:** `ols_is_projection`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

