# Implicit bias homogeneous in labels

**ID:** `implicit-bias-smul-y`  
**Chapter:** Ch12 (Bach §12.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/implicit-bias-smul-y/`](../../../tasks/implicit-bias-smul-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Implicit bias homogeneous in labels (scalar multiplication)

**Concept ID:** `implicit-bias-smul-y`
**Chapter:** Ch 12
**Section:** 12.1.1 Least-Squares Regression
**Pages:** 344-345
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
> [Bach, §12.1.1, eq. (12.1)-(12.2), closed-form GD limit.]
> Since K = XX⊤ is invertible, … θ_t = X⊤ α_t converges to X⊤ K⁻¹ y. One may have
> recognized in X⊤ K⁻¹ = X⊤(XX⊤)⁻¹ the pseudo-inverse of X, and hence X⊤ K⁻¹ y is
> the minimum ℓ₂-norm solution of {Xθ = y}.

> The implicit-bias map T(y) := X⊤(XX⊤)⁻¹ y is linear, hence positively (and
> negatively) homogeneous:
>   T(c · y) = c · T(y)        for all c ∈ ℝ, y ∈ ℝⁿ.

## Proof (verbatim)
> [Trivial corollary of the closed-form expression; Bach does not isolate it.]
> By definition, T(y) = M y where M := X⊤(XX⊤)⁻¹ ∈ ℝᵈˣⁿ is a fixed matrix. For any
> scalar c ∈ ℝ,
>   T(c·y) = M(c·y) = c·(M y) = c·T(y),
> by the scalar–matrix–vector identity M(cy) = c(My).
>
> Equivalently, from the Lagrangian dual eq. (12.2):
>   sup_α α⊤(c·y) − ½ α⊤ K α
> has unique optimizer α* = K⁻¹(c·y) = c·K⁻¹y, and θ* = X⊤ α* = c·T(y).

## Notes
- Lean target `implicitBias_smul_y` anchors the homogeneity property of the
  implicit-bias map y ↦ X⊤(XX⊤)⁻¹y.
- Source justification: §12.1.1 derives the closed form X⊤(XX⊤)⁻¹y as the GD limit;
  the pseudoinverse X⁺ y is by construction a linear function of y, hence
  homogeneous.
- Technique in one line: scalar–matrix multiplication commutes.
- Pairs with `implicit-bias-add-y` (additivity) to give linearity, which together
  with `implicit-bias-zero-labels` (T(0)=0) reconstructs the full implicit-bias
  identity from elementary parts on the Lean side.
- No ambiguities.

## Prerequisites (Bach's dependency graph)

- [`implicit-bias-full-rank`](./implicit-bias-full-rank.md) — Implicit bias of GD = OLS (full-rank case)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch12_Overparameterized/ImplicitBias.lean`
- **Theorem/def name:** `implicitBias_smul_y`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

