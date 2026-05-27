# OLS closed form: β̂ = (XᵀX)⁻¹Xᵀy

**ID:** `ols-closed-form`  
**Chapter:** Ch03 (Bach §3.3.1, p. 47)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `OLS`

## Statement

_See textbook excerpt below or [`tasks/ols-closed-form/`](../../../tasks/ols-closed-form/) if available._

## Bach's textbook treatment

# Book excerpt — `ols-closed-form` (Bach 2024 §3.3.1, pp. 47–48)

> **Definition 3.1 (OLS).** When `Φ` has full column rank, the
> minimizer of `R̂(θ) = (1/n) ‖y − Φ θ‖²` is unique and called the
> ordinary least-squares (OLS) estimator.
>
> **Proposition 3.1.** When `Φ` has full column rank, the OLS estimator
> exists, is unique, and is given by
>
>     θ̂ = (ΦᵀΦ)⁻¹ Φᵀ y.
>
> *Proof.* `R̂` is coercive, continuous, differentiable, so a minimizer
> `θ̂ ∈ ℝᵈ` must satisfy the gradient condition `R̂'(θ̂) = 0`. Expanding
> the square gives `R̂(θ) = (1/n)(‖y‖² − 2 θᵀ Φᵀ y + θᵀ ΦᵀΦ θ)`, and
> `R̂'(θ) = (2/n)(ΦᵀΦ θ − Φᵀ y)`. Setting the gradient to zero yields
> the **normal equation**:
>
>     ΦᵀΦ θ̂ = Φᵀ y.
>
> The unique solution of the normal equation is `θ̂ = (ΦᵀΦ)⁻¹ Φᵀ y`.

## Lean target

The file `LTFP/Ch03_LinearLeastSquares/OLS.lean` already defines

    noncomputable def olsEstimator
        (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) : Fin d → ℝ :=
      ((Xᵀ * X)⁻¹ * Xᵀ).mulVec y

The theorem is the **normal equation** that this estimator satisfies
(the closed-form characterization, modulo the gradient/minimization
narrative which requires more Mathlib calculus than is profitable here):

    theorem ols_closed_form {n d : ℕ}
        (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
        (hX : IsUnit (Xᵀ * X).det) :
        (Xᵀ * X) *ᵥ olsEstimator X y = Xᵀ *ᵥ y

Proof sketch (one-liner): unfold `olsEstimator`, then
`((XᵀX) * (XᵀX)⁻¹ * Xᵀ) *ᵥ y = Xᵀ *ᵥ y` via
`Matrix.mul_nonsing_inv` (or `Matrix.mul_nonsing_inv_cancel_left`) and
`Matrix.mulVec_mulVec`.

## Acceptable smaller fallback

If `IsUnit (Xᵀ * X).det` causes friction (e.g. you want `Invertible`
typeclass instead), use `[Invertible (Xᵀ * X)]` and the
`Matrix.mul_invOf` family. Either form is fine.

If even the normal equation gets stuck, fall back to a one-liner
unit-test–style identity such as `Xᵀ *ᵥ y = (Xᵀ * 1) *ᵥ y` via
`Matrix.mul_one`. (This is much weaker, so prefer the normal equation
if at all possible.)

**No `sorry`, no `admit`, no `True`** — the body must be a real Lean
proof. Useful Mathlib lemmas: `Matrix.mul_nonsing_inv`,
`Matrix.mul_nonsing_inv_cancel_left`, `Matrix.mulVec_mulVec`,
`Matrix.mul_assoc`, `Matrix.one_mulVec`.

## Prerequisites (Bach's dependency graph)

- [`empirical-risk`](./empirical-risk.md) — Empirical risk R̂_n(f)
- [`quadratic-form-min`](./quadratic-form-min.md) — Minimization of a positive-definite quadratic form

## Dependents (concepts that use this)

- [`implicit-bias-full-rank`](./implicit-bias-full-rank.md) — Implicit bias of GD = OLS (full-rank case)
- [`ols-add-y`](./ols-add-y.md) — OLS linear in labels
- [`ols-fixed-design-bias-variance`](./ols-fixed-design-bias-variance.md) — Fixed-design OLS bias-variance decomposition
- [`ols-geometric`](./ols-geometric.md) — OLS as orthogonal projection onto col(X)
- [`ols-smul-y`](./ols-smul-y.md) — OLS homogeneous in labels
- [`ridge-closed-form`](./ridge-closed-form.md) — Ridge closed form: β̂_λ = (XᵀX + nλI)⁻¹Xᵀy

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/OLS.lean`
- **Theorem/def name:** `ols_closed_form`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

