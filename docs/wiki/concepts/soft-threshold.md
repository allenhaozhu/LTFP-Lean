# Soft-thresholding operator (closed form for 1-D Lasso)

**ID:** `soft-threshold`  
**Chapter:** Ch08 (Bach §8.3.1, p. 233)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Lasso/Sparse`

## Statement

_See textbook excerpt below or [`tasks/soft-threshold/`](../../../tasks/soft-threshold/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Soft-thresholding operator (closed form for 1-D Lasso)

**Concept ID:** `soft-threshold`
**Chapter:** Ch 8
**Section:** 8.3.1 (One-dimensional problem) — operator definition
**Pages:** 232
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Verbatim from §8.3.1 "One-dimensional problem" (p. 232):

> [The minimizer of F(θ) = ½(y − θ)² + λ|θ| for λ > 0 is]
>
>   θ*_λ(y) = 0       if |y| ≤ λ,
>   θ*_λ(y) = y − λ   for y > λ,
>   θ*_λ(y) = y + λ   for y < −λ,
>
> which can be put together as
>
>   **θ*_λ(y) = max{|y| − λ, 0} · sign(y)**,
>
> which is depicted here. This is referred to as **"iterative soft thresholding"** (this will be useful for the proximal methods discussed next).

The same operator appears coordinate-wise in proximal/coordinate descent algorithms for the multivariate Lasso (pp. 232–233):

> Iterative soft-thresholding: We can apply proximal methods (section 5.2.5) to the objective function of the form F(θ) + λ‖θ‖₁ … This leads to (θₜ)ⱼ = max{|(ηₜ)ⱼ| − λ/L, 0} · sign((ηₜ)ⱼ), for ηₜ = θₜ₋₁ − (1/L) F'(θₜ₋₁).

## Proof (verbatim)

(definition; correctness as the 1-D Lasso minimizer is the content of `lasso-kkt`)

## Notes

- This is the **definition** of the soft-thresholding operator S_λ(y) := max(|y| − λ, 0) · sign(y).
- Bach uses "iterative soft thresholding" both for the scalar operator and (coordinate-wise) for the proximal-gradient update of the multivariate Lasso.
- The closed form is the unique minimizer of the 1-D Lasso objective (proved separately in `lasso-kkt`).
- **Sign convention**: Bach's formula gives S_λ(0) = max(−λ, 0) · sign(0) = 0 · sign(0) = 0 regardless of sign(0) convention (assuming λ ≥ 0).
- **Bach's proof technique** (for the closed form itself): direct derivation from left/right derivatives at θ = 0 of the 1-D objective; convexity guarantees the resulting piecewise-affine map is the minimizer.
- Lean target `LTFP/Ch08_Sparse/L1.lean#softThreshold` should define S_λ(y) = max(|y| − λ, 0) * sign(y), matching Bach's formula.

## Prerequisites (Bach's dependency graph)

- [`l1-norm`](./l1-norm.md) — ℓ₁ norm: sum of absolute values

## Dependents (concepts that use this)

- [`lasso-kkt`](./lasso-kkt.md) — Scalar Lasso KKT (soft-thresholding minimizer)
- [`soft-threshold-at-lam`](./soft-threshold-at-lam.md) — Soft threshold at level lam = 0 at z = lam
- [`soft-threshold-zero-zero`](./soft-threshold-zero-zero.md) — Soft threshold of 0 at level 0 = 0

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L1.lean`
- **Theorem/def name:** `softThreshold`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

